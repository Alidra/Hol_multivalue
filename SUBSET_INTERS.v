Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_INTERS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
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
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3358036 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3358037 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (@SUBSET _87290 s t) = (term0 _87290 s t).
Proof. exact (@lem3358036 _87290 s t). Qed.
Lemma lem3358038 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term1 _87290 s f) = (term2 _87290 s f).
Proof. exact (@lem3358037 _87290 s (@INTERS _87290 f)). Qed.
Lemma lem3358045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358046 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term3 _87290 s f) = (term4 _87290 s f).
Proof. exact (MK_COMB (@lem3358045) (@lem3358038 _87290 s f)). Qed.
Lemma lem3358054 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3358055 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (@SUBSET _87290 s t) = (term0 _87290 s t).
Proof. exact (@lem3358054 _87290 s t). Qed.
Lemma lem3358062 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) : (term5 _87290 t f) = (term5 _87290 t f).
Proof. exact (eq_refl (term5 _87290 t f)). Qed.
Lemma lem3358063 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term6 _87290 f s t) = (term7 _87290 f s t).
Proof. exact (MK_COMB (@lem3358062 _87290 t f) (@lem3358055 _87290 s t)). Qed.
Lemma lem3358066 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term8 _87290 f s) = (term9 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358063 _87290 f s t)). Qed.
Lemma lem3358067 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358068 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term10 _87290 f s) = (term11 _87290 f s).
Proof. exact (MK_COMB (@lem3358067 _87290) (@lem3358066 _87290 f s)). Qed.
Lemma lem3358073 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : ((term1 _87290 s f) = (term10 _87290 f s)) = ((term2 _87290 s f) = (term11 _87290 f s)).
Proof. exact (MK_COMB (@lem3358046 _87290 s f) (@lem3358068 _87290 f s)). Qed.
Lemma lem3358078 {_87290 : Type'} (s : _87290 -> Prop) : (term12 _87290 s) = (term13 _87290 s).
Proof. exact (fun_ext (fun f : type686 _87290 => @lem3358073 _87290 f s)). Qed.
Lemma lem3358079 {_87290 : Type'} : (@all ((_87290 -> Prop) -> Prop)) = (@all ((_87290 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87290 -> Prop) -> Prop))). Qed.
Lemma lem3358080 {_87290 : Type'} (s : _87290 -> Prop) : (term14 _87290 s) = (term15 _87290 s).
Proof. exact (MK_COMB (@lem3358079 _87290) (@lem3358078 _87290 s)). Qed.
Lemma lem3358085 {_87290 : Type'} : (term16 _87290) = (term17 _87290).
Proof. exact (fun_ext (fun s : _87290 -> Prop => @lem3358080 _87290 s)). Qed.
Lemma lem3358086 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358087 {_87290 : Type'} : (term18 _87290) = (term19 _87290).
Proof. exact (MK_COMB (@lem3358086 _87290) (@lem3358085 _87290)). Qed.
Lemma lem3358092 {_87290 : Type'} : (term19 _87290) = (term18 _87290).
Proof. exact (SYM (@lem3358087 _87290)). Qed.
Lemma lem3358110 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3358111 {_87290 : Type'} (P : _87290 -> Prop) (x : _87290) : (@IN _87290 x P) = (P x).
Proof. exact (@lem3358110 _87290 P x). Qed.
Lemma lem3358112 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (@IN _87290 x s) = (s x).
Proof. exact (@lem3358111 _87290 s x). Qed.
Lemma lem3358113 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3358114 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term20 _87290 x s) = (term21 _87290 s x).
Proof. exact (MK_COMB (@lem3358113) (@lem3358112 _87290 s x)). Qed.
Lemma lem3358116 {A : Type'} (s : type686 A) (x : A) : (term22 A x s) = (term23 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3358117 {_87290 : Type'} (s : type686 _87290) (x : _87290) : (term22 _87290 x s) = (term23 _87290 s x).
Proof. exact (@lem3358116 _87290 s x). Qed.
Lemma lem3358118 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term22 _87290 x f) = (term23 _87290 f x).
Proof. exact (@lem3358117 _87290 f x). Qed.
Lemma lem3358126 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3358127 {_87290 : Type'} (P : type686 _87290) (x : _87290 -> Prop) : (@IN (_87290 -> Prop) x P) = (P x).
Proof. exact (@lem3358126 (_87290 -> Prop) P x). Qed.
Lemma lem3358128 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (@IN (_87290 -> Prop) t f) = (f t).
Proof. exact (@lem3358127 _87290 f t). Qed.
Lemma lem3358129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3358130 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term5 _87290 t f) = (term24 _87290 f t).
Proof. exact (MK_COMB (@lem3358129) (@lem3358128 _87290 f t)). Qed.
Lemma lem3358132 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3358133 {_87290 : Type'} (P : _87290 -> Prop) (x : _87290) : (@IN _87290 x P) = (P x).
Proof. exact (@lem3358132 _87290 P x). Qed.
Lemma lem3358134 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (@IN _87290 x t) = (t x).
Proof. exact (@lem3358133 _87290 t x). Qed.
Lemma lem3358135 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term25 _87290 f x t) = (term26 _87290 f t x).
Proof. exact (MK_COMB (@lem3358130 _87290 f t) (@lem3358134 _87290 t x)). Qed.
Lemma lem3358138 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term27 _87290 f x) = (term28 _87290 f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358135 _87290 f t x)). Qed.
Lemma lem3358139 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358140 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term23 _87290 f x) = (term29 _87290 f x).
Proof. exact (MK_COMB (@lem3358139 _87290) (@lem3358138 _87290 f x)). Qed.
Lemma lem3358145 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term22 _87290 x f) = (term29 _87290 f x).
Proof. exact (TRANS (@lem3358118 _87290 f x) (@lem3358140 _87290 f x)). Qed.
Lemma lem3358146 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term30 _87290 s x f) = (term31 _87290 s f x).
Proof. exact (MK_COMB (@lem3358114 _87290 s x) (@lem3358145 _87290 f x)). Qed.
Lemma lem3358149 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term32 _87290 s f) = (term33 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3358146 _87290 s f x)). Qed.
Lemma lem3358150 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3358151 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term2 _87290 s f) = (term34 _87290 s f).
Proof. exact (MK_COMB (@lem3358150 _87290) (@lem3358149 _87290 s f)). Qed.
Lemma lem3358156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358157 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term4 _87290 s f) = (term35 _87290 s f).
Proof. exact (MK_COMB (@lem3358156) (@lem3358151 _87290 s f)). Qed.
Lemma lem3358165 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3358166 {_87290 : Type'} (P : type686 _87290) (x : _87290 -> Prop) : (@IN (_87290 -> Prop) x P) = (P x).
Proof. exact (@lem3358165 (_87290 -> Prop) P x). Qed.
Lemma lem3358167 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (@IN (_87290 -> Prop) t f) = (f t).
Proof. exact (@lem3358166 _87290 f t). Qed.
Lemma lem3358168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3358169 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term5 _87290 t f) = (term24 _87290 f t).
Proof. exact (MK_COMB (@lem3358168) (@lem3358167 _87290 f t)). Qed.
Lemma lem3358177 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3358178 {_87290 : Type'} (P : _87290 -> Prop) (x : _87290) : (@IN _87290 x P) = (P x).
Proof. exact (@lem3358177 _87290 P x). Qed.
Lemma lem3358179 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (@IN _87290 x s) = (s x).
Proof. exact (@lem3358178 _87290 s x). Qed.
Lemma lem3358180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3358181 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term20 _87290 x s) = (term21 _87290 s x).
Proof. exact (MK_COMB (@lem3358180) (@lem3358179 _87290 s x)). Qed.
Lemma lem3358183 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3358184 {_87290 : Type'} (P : _87290 -> Prop) (x : _87290) : (@IN _87290 x P) = (P x).
Proof. exact (@lem3358183 _87290 P x). Qed.
Lemma lem3358185 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (@IN _87290 x t) = (t x).
Proof. exact (@lem3358184 _87290 t x). Qed.
Lemma lem3358186 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term36 _87290 s x t) = (term37 _87290 s t x).
Proof. exact (MK_COMB (@lem3358181 _87290 s x) (@lem3358185 _87290 t x)). Qed.
Lemma lem3358189 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term38 _87290 s t) = (term39 _87290 s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358186 _87290 s t x)). Qed.
Lemma lem3358190 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3358191 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term0 _87290 s t) = (term40 _87290 s t).
Proof. exact (MK_COMB (@lem3358190 _87290) (@lem3358189 _87290 s t)). Qed.
Lemma lem3358196 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term7 _87290 f s t) = (term41 _87290 f s t).
Proof. exact (MK_COMB (@lem3358169 _87290 f t) (@lem3358191 _87290 s t)). Qed.
Lemma lem3358199 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term9 _87290 f s) = (term42 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358196 _87290 f s t)). Qed.
Lemma lem3358200 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358201 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term11 _87290 f s) = (term43 _87290 f s).
Proof. exact (MK_COMB (@lem3358200 _87290) (@lem3358199 _87290 f s)). Qed.
Lemma lem3358206 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : ((term2 _87290 s f) = (term11 _87290 f s)) = ((term34 _87290 s f) = (term43 _87290 f s)).
Proof. exact (MK_COMB (@lem3358157 _87290 s f) (@lem3358201 _87290 f s)). Qed.
Lemma lem3358209 {_87290 : Type'} (s : _87290 -> Prop) : (term13 _87290 s) = (term44 _87290 s).
Proof. exact (fun_ext (fun f : type686 _87290 => @lem3358206 _87290 f s)). Qed.
Lemma lem3358210 {_87290 : Type'} : (@all ((_87290 -> Prop) -> Prop)) = (@all ((_87290 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87290 -> Prop) -> Prop))). Qed.
Lemma lem3358211 {_87290 : Type'} (s : _87290 -> Prop) : (term15 _87290 s) = (term45 _87290 s).
Proof. exact (MK_COMB (@lem3358210 _87290) (@lem3358209 _87290 s)). Qed.
Lemma lem3358216 {_87290 : Type'} : (term17 _87290) = (term46 _87290).
Proof. exact (fun_ext (fun s : _87290 -> Prop => @lem3358211 _87290 s)). Qed.
Lemma lem3358217 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358218 {_87290 : Type'} : (term19 _87290) = (term47 _87290).
Proof. exact (MK_COMB (@lem3358217 _87290) (@lem3358216 _87290)). Qed.
Lemma lem3358223 {_87290 : Type'} : (term47 _87290) = (term19 _87290).
Proof. exact (SYM (@lem3358218 _87290)). Qed.
Lemma lem3358225 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3358226 {_87290 : Type'} : (term47 _87290) = (term49 _87290).
Proof. exact (@lem3358225 (term47 _87290)). Qed.
Lemma lem3358227 {_87290 : Type'} : (term49 _87290) = (term47 _87290).
Proof. exact (SYM (@lem3358226 _87290)). Qed.
Lemma lem3358228 {_87290 : Type'} (h1 : term50 _87290) : term50 _87290.
Proof. exact (h1). Qed.
Lemma lem3358231 {_87290 : Type'} (h1 : term49 _87290) : term49 _87290.
Proof. exact (h1). Qed.
Lemma lem3358232 {_87290 : Type'} : term51 _87290.
Proof. exact (fun h0 : term49 _87290 => @lem3358231 _87290 h0). Qed.
Lemma lem3358233 {_87290 : Type'} (h1 : term51 _87290) : term51 _87290.
Proof. exact (h1). Qed.
Lemma lem3358234 {_87290 : Type'} (h1 : term49 _87290) : term49 _87290.
Proof. exact (h1). Qed.
Lemma lem3358235 {_87290 : Type'} (h1 : term49 _87290) (h2 : term51 _87290) : term49 _87290.
Proof. exact (@lem3358233 _87290 h2 (@lem3358234 _87290 h1)). Qed.
Lemma lem3358236 {_87290 : Type'} (h1 : term49 _87290) : term52 _87290.
Proof. exact (fun h0 : term51 _87290 => @lem3358235 _87290 h1 h0). Qed.
Lemma lem3358237 {_87290 : Type'} (h1 : term51 _87290) : term51 _87290.
Proof. exact (h1). Qed.
Lemma lem3358238 {_87290 : Type'} (h1 : term49 _87290) (h2 : term51 _87290) : term49 _87290.
Proof. exact (@lem3358236 _87290 h1 (@lem3358237 _87290 h2)). Qed.
Lemma lem3358239 {_87290 : Type'} (h1 : term51 _87290) : term51 _87290.
Proof. exact (fun h0 : term49 _87290 => @lem3358238 _87290 h0 h1). Qed.
Lemma lem3358240 {_87290 : Type'} : term53 _87290.
Proof. exact (fun h0 : term51 _87290 => @lem3358239 _87290 h0). Qed.
Lemma lem3358243 {_87290 : Type'} : term51 _87290.
Proof. exact (@lem3358240 _87290 (@lem3358232 _87290)). Qed.
Lemma lem3358244 {_87290 : Type'} : term51 _87290.
Proof. exact (@lem3358243 _87290). Qed.
Lemma lem3358246 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3358247 {_87290 : Type'} : (term49 _87290) = (term54 _87290).
Proof. exact (@lem3358246 (term50 _87290)). Qed.
Lemma lem3358249 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3358250 {_87290 : Type'} : (term54 _87290) = (term47 _87290).
Proof. exact (@lem3358249 (term47 _87290)). Qed.
Lemma lem3358287 {_87290 : Type'} : (term49 _87290) = (term47 _87290).
Proof. exact (TRANS (@lem3358247 _87290) (@lem3358250 _87290)). Qed.
Lemma lem3358292 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term37 _87290 s t x) = (term37 _87290 s t x).
Proof. exact (eq_refl (term37 _87290 s t x)). Qed.
Lemma lem3358293 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term39 _87290 s t) = (term39 _87290 s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358292 _87290 s t x)). Qed.
Lemma lem3358294 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3358295 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term40 _87290 s t) = (term40 _87290 s t).
Proof. exact (MK_COMB (@lem3358294 _87290) (@lem3358293 _87290 s t)). Qed.
Lemma lem3358298 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term24 _87290 f t) = (term24 _87290 f t).
Proof. exact (eq_refl (term24 _87290 f t)). Qed.
Lemma lem3358299 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term41 _87290 f s t) = (term41 _87290 f s t).
Proof. exact (MK_COMB (@lem3358298 _87290 f t) (@lem3358295 _87290 s t)). Qed.
Lemma lem3358300 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term42 _87290 f s) = (term42 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358299 _87290 f s t)). Qed.
Lemma lem3358301 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358302 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term43 _87290 f s) = (term43 _87290 f s).
Proof. exact (MK_COMB (@lem3358301 _87290) (@lem3358300 _87290 f s)). Qed.
Lemma lem3358307 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term26 _87290 f t x) = (term26 _87290 f t x).
Proof. exact (eq_refl (term26 _87290 f t x)). Qed.
Lemma lem3358308 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term28 _87290 f x) = (term28 _87290 f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358307 _87290 f t x)). Qed.
Lemma lem3358309 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358310 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term29 _87290 f x) = (term29 _87290 f x).
Proof. exact (MK_COMB (@lem3358309 _87290) (@lem3358308 _87290 f x)). Qed.
Lemma lem3358313 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term21 _87290 s x) = (term21 _87290 s x).
Proof. exact (eq_refl (term21 _87290 s x)). Qed.
Lemma lem3358314 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term31 _87290 s f x) = (term31 _87290 s f x).
Proof. exact (MK_COMB (@lem3358313 _87290 s x) (@lem3358310 _87290 f x)). Qed.
Lemma lem3358315 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term33 _87290 s f) = (term33 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3358314 _87290 s f x)). Qed.
Lemma lem3358316 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3358317 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term34 _87290 s f) = (term34 _87290 s f).
Proof. exact (MK_COMB (@lem3358316 _87290) (@lem3358315 _87290 s f)). Qed.
Lemma lem3358318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358319 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term35 _87290 s f) = (term35 _87290 s f).
Proof. exact (MK_COMB (@lem3358318) (@lem3358317 _87290 s f)). Qed.
Lemma lem3358320 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : ((term34 _87290 s f) = (term43 _87290 f s)) = ((term34 _87290 s f) = (term43 _87290 f s)).
Proof. exact (MK_COMB (@lem3358319 _87290 s f) (@lem3358302 _87290 f s)). Qed.
Lemma lem3358321 {_87290 : Type'} (s : _87290 -> Prop) : (term44 _87290 s) = (term44 _87290 s).
Proof. exact (fun_ext (fun f : type686 _87290 => @lem3358320 _87290 f s)). Qed.
Lemma lem3358322 {_87290 : Type'} : (@all ((_87290 -> Prop) -> Prop)) = (@all ((_87290 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_87290 -> Prop) -> Prop))). Qed.
Lemma lem3358323 {_87290 : Type'} (s : _87290 -> Prop) : (term45 _87290 s) = (term45 _87290 s).
Proof. exact (MK_COMB (@lem3358322 _87290) (@lem3358321 _87290 s)). Qed.
Lemma lem3358324 {_87290 : Type'} : (term46 _87290) = (term46 _87290).
Proof. exact (fun_ext (fun s : _87290 -> Prop => @lem3358323 _87290 s)). Qed.
Lemma lem3358325 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358326 {_87290 : Type'} : (term47 _87290) = (term47 _87290).
Proof. exact (MK_COMB (@lem3358325 _87290) (@lem3358324 _87290)). Qed.
Lemma lem3358373 {_87290 : Type'} : (term49 _87290) = (term47 _87290).
Proof. exact (TRANS (@lem3358287 _87290) (@lem3358326 _87290)). Qed.
Lemma lem3358374 {_87290 : Type'} : (term47 _87290) = (term49 _87290).
Proof. exact (SYM (@lem3358373 _87290)). Qed.
Lemma lem3358376 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3358377 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : ((term34 _87290 s f) = (term43 _87290 f s)) = (term56 _87290 f s).
Proof. exact (@lem3358376 ((term34 _87290 s f) = (term43 _87290 f s))). Qed.
Lemma lem3358378 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term56 _87290 f s) = ((term34 _87290 s f) = (term43 _87290 f s)).
Proof. exact (SYM (@lem3358377 _87290 f s)). Qed.
Lemma lem3358379 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (h1 : term57 _87290 f s) : term57 _87290 f s.
Proof. exact (h1). Qed.
Lemma lem3358390 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term58 _87290 f t x) = (term59 _87290 f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem3358395 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term26 _87290 f t x) = (term60 _87290 f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3358396 {_87290 : Type'} (P : type686 _87290) : (term61 _87290 P) = (term62 _87290 P).
Proof. exact (@lem18392 (_87290 -> Prop) P). Qed.
Lemma lem3358397 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term63 _87290 f x) = (term64 _87290 f x).
Proof. exact (@lem3358396 _87290 (term28 _87290 f x)). Qed.
Lemma lem3358398 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term65 _87290 f x t) = (term26 _87290 f t x).
Proof. exact (eq_refl (term65 _87290 f x t)). Qed.
Lemma lem3358399 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3358400 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term66 _87290 f x t) = (term58 _87290 f t x).
Proof. exact (MK_COMB (@lem3358399) (@lem3358398 _87290 f t x)). Qed.
Lemma lem3358401 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term66 _87290 f x t) = (term59 _87290 f t x).
Proof. exact (TRANS (@lem3358400 _87290 f t x) (@lem3358390 _87290 f t x)). Qed.
Lemma lem3358402 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term67 _87290 f x) = (term68 _87290 f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358401 _87290 f t x)). Qed.
Lemma lem3358403 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358404 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term64 _87290 f x) = (term69 _87290 f x).
Proof. exact (MK_COMB (@lem3358403 _87290) (@lem3358402 _87290 f x)). Qed.
Lemma lem3358405 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term63 _87290 f x) = (term69 _87290 f x).
Proof. exact (TRANS (@lem3358397 _87290 f x) (@lem3358404 _87290 f x)). Qed.
Lemma lem3358406 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term28 _87290 f x) = (term70 _87290 f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358395 _87290 f t x)). Qed.
Lemma lem3358407 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358408 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term29 _87290 f x) = (term71 _87290 f x).
Proof. exact (MK_COMB (@lem3358407 _87290) (@lem3358406 _87290 f x)). Qed.
Lemma lem3358410 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term72 _87290 s x) = (term72 _87290 s x).
Proof. exact (eq_refl (term72 _87290 s x)). Qed.
Lemma lem3358411 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term73 _87290 s f x) = (term74 _87290 s f x).
Proof. exact (MK_COMB (@lem3358410 _87290 s x) (@lem3358405 _87290 f x)). Qed.
Lemma lem3358412 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term75 _87290 s f x) = (term73 _87290 s f x).
Proof. exact (@lem17362 (s x) (term29 _87290 f x)). Qed.
Lemma lem3358413 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term75 _87290 s f x) = (term74 _87290 s f x).
Proof. exact (TRANS (@lem3358412 _87290 s f x) (@lem3358411 _87290 s f x)). Qed.
Lemma lem3358415 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term76 _87290 s x) = (term76 _87290 s x).
Proof. exact (eq_refl (term76 _87290 s x)). Qed.
Lemma lem3358416 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term77 _87290 s f x) = (term78 _87290 s f x).
Proof. exact (MK_COMB (@lem3358415 _87290 s x) (@lem3358408 _87290 f x)). Qed.
Lemma lem3358417 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term31 _87290 s f x) = (term77 _87290 s f x).
Proof. exact (@lem17265 (s x) (term29 _87290 f x)). Qed.
Lemma lem3358418 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term31 _87290 s f x) = (term78 _87290 s f x).
Proof. exact (TRANS (@lem3358417 _87290 s f x) (@lem3358416 _87290 s f x)). Qed.
Lemma lem3358419 {_87290 : Type'} (P : _87290 -> Prop) : (term79 _87290 P) = (term80 _87290 P).
Proof. exact (@lem18392 _87290 P). Qed.
Lemma lem3358420 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term81 _87290 s f) = (term82 _87290 s f).
Proof. exact (@lem3358419 _87290 (term33 _87290 s f)). Qed.
Lemma lem3358421 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term83 _87290 s f x) = (term31 _87290 s f x).
Proof. exact (eq_refl (term83 _87290 s f x)). Qed.
Lemma lem3358422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3358423 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term84 _87290 s f x) = (term75 _87290 s f x).
Proof. exact (MK_COMB (@lem3358422) (@lem3358421 _87290 s f x)). Qed.
Lemma lem3358424 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term84 _87290 s f x) = (term74 _87290 s f x).
Proof. exact (TRANS (@lem3358423 _87290 s f x) (@lem3358413 _87290 s f x)). Qed.
Lemma lem3358425 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term85 _87290 s f) = (term86 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3358424 _87290 s f x)). Qed.
Lemma lem3358426 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358427 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term82 _87290 s f) = (term87 _87290 s f).
Proof. exact (MK_COMB (@lem3358426 _87290) (@lem3358425 _87290 s f)). Qed.
Lemma lem3358428 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term81 _87290 s f) = (term87 _87290 s f).
Proof. exact (TRANS (@lem3358420 _87290 s f) (@lem3358427 _87290 s f)). Qed.
Lemma lem3358429 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term33 _87290 s f) = (term88 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3358418 _87290 s f x)). Qed.
Lemma lem3358430 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3358431 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term34 _87290 s f) = (term89 _87290 s f).
Proof. exact (MK_COMB (@lem3358430 _87290) (@lem3358429 _87290 s f)). Qed.
Lemma lem3358442 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term90 _87290 s t x) = (term91 _87290 s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3358447 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term37 _87290 s t x) = (term92 _87290 s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3358448 {_87290 : Type'} (P : _87290 -> Prop) : (term79 _87290 P) = (term80 _87290 P).
Proof. exact (@lem18392 _87290 P). Qed.
Lemma lem3358449 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term93 _87290 s t) = (term94 _87290 s t).
Proof. exact (@lem3358448 _87290 (term39 _87290 s t)). Qed.
Lemma lem3358450 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term95 _87290 s t x) = (term37 _87290 s t x).
Proof. exact (eq_refl (term95 _87290 s t x)). Qed.
Lemma lem3358451 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3358452 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term96 _87290 s t x) = (term90 _87290 s t x).
Proof. exact (MK_COMB (@lem3358451) (@lem3358450 _87290 s t x)). Qed.
Lemma lem3358453 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term96 _87290 s t x) = (term91 _87290 s t x).
Proof. exact (TRANS (@lem3358452 _87290 s t x) (@lem3358442 _87290 s t x)). Qed.
Lemma lem3358454 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term97 _87290 s t) = (term98 _87290 s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358453 _87290 s t x)). Qed.
Lemma lem3358455 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358456 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term94 _87290 s t) = (term99 _87290 s t).
Proof. exact (MK_COMB (@lem3358455 _87290) (@lem3358454 _87290 s t)). Qed.
Lemma lem3358457 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term93 _87290 s t) = (term99 _87290 s t).
Proof. exact (TRANS (@lem3358449 _87290 s t) (@lem3358456 _87290 s t)). Qed.
Lemma lem3358458 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term39 _87290 s t) = (term100 _87290 s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358447 _87290 s t x)). Qed.
Lemma lem3358459 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3358460 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term40 _87290 s t) = (term101 _87290 s t).
Proof. exact (MK_COMB (@lem3358459 _87290) (@lem3358458 _87290 s t)). Qed.
Lemma lem3358462 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term102 _87290 f t) = (term102 _87290 f t).
Proof. exact (eq_refl (term102 _87290 f t)). Qed.
Lemma lem3358463 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term103 _87290 f s t) = (term104 _87290 f s t).
Proof. exact (MK_COMB (@lem3358462 _87290 f t) (@lem3358457 _87290 s t)). Qed.
Lemma lem3358464 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term105 _87290 f s t) = (term103 _87290 f s t).
Proof. exact (@lem17362 (f t) (term40 _87290 s t)). Qed.
Lemma lem3358465 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term105 _87290 f s t) = (term104 _87290 f s t).
Proof. exact (TRANS (@lem3358464 _87290 f s t) (@lem3358463 _87290 f s t)). Qed.
Lemma lem3358467 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term106 _87290 f t) = (term106 _87290 f t).
Proof. exact (eq_refl (term106 _87290 f t)). Qed.
Lemma lem3358468 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term107 _87290 f s t) = (term108 _87290 f s t).
Proof. exact (MK_COMB (@lem3358467 _87290 f t) (@lem3358460 _87290 s t)). Qed.
Lemma lem3358469 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term41 _87290 f s t) = (term107 _87290 f s t).
Proof. exact (@lem17265 (f t) (term40 _87290 s t)). Qed.
Lemma lem3358470 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term41 _87290 f s t) = (term108 _87290 f s t).
Proof. exact (TRANS (@lem3358469 _87290 f s t) (@lem3358468 _87290 f s t)). Qed.
Lemma lem3358471 {_87290 : Type'} (P : type686 _87290) : (term61 _87290 P) = (term62 _87290 P).
Proof. exact (@lem18392 (_87290 -> Prop) P). Qed.
Lemma lem3358472 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term109 _87290 f s) = (term110 _87290 f s).
Proof. exact (@lem3358471 _87290 (term42 _87290 f s)). Qed.
Lemma lem3358473 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term111 _87290 f s t) = (term41 _87290 f s t).
Proof. exact (eq_refl (term111 _87290 f s t)). Qed.
Lemma lem3358474 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3358475 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term112 _87290 f s t) = (term105 _87290 f s t).
Proof. exact (MK_COMB (@lem3358474) (@lem3358473 _87290 f s t)). Qed.
Lemma lem3358476 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term112 _87290 f s t) = (term104 _87290 f s t).
Proof. exact (TRANS (@lem3358475 _87290 f s t) (@lem3358465 _87290 f s t)). Qed.
Lemma lem3358477 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term113 _87290 f s) = (term114 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358476 _87290 f s t)). Qed.
Lemma lem3358478 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358479 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term110 _87290 f s) = (term115 _87290 f s).
Proof. exact (MK_COMB (@lem3358478 _87290) (@lem3358477 _87290 f s)). Qed.
Lemma lem3358480 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term109 _87290 f s) = (term115 _87290 f s).
Proof. exact (TRANS (@lem3358472 _87290 f s) (@lem3358479 _87290 f s)). Qed.
Lemma lem3358481 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term42 _87290 f s) = (term116 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358470 _87290 f s t)). Qed.
Lemma lem3358482 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3358483 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term43 _87290 f s) = (term117 _87290 f s).
Proof. exact (MK_COMB (@lem3358482 _87290) (@lem3358481 _87290 f s)). Qed.
Lemma lem3358484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3358485 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term118 _87290 s f) = (term119 _87290 s f).
Proof. exact (MK_COMB (@lem3358484) (@lem3358428 _87290 s f)). Qed.
Lemma lem3358486 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term120 _87290 f s) = (term121 _87290 f s).
Proof. exact (MK_COMB (@lem3358485 _87290 s f) (@lem3358483 _87290 f s)). Qed.
Lemma lem3358487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3358488 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term122 _87290 s f) = (term123 _87290 s f).
Proof. exact (MK_COMB (@lem3358487) (@lem3358431 _87290 s f)). Qed.
Lemma lem3358489 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term124 _87290 f s) = (term125 _87290 f s).
Proof. exact (MK_COMB (@lem3358488 _87290 s f) (@lem3358480 _87290 f s)). Qed.
Lemma lem3358490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3358491 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term126 _87290 f s) = (term127 _87290 f s).
Proof. exact (MK_COMB (@lem3358490) (@lem3358489 _87290 f s)). Qed.
Lemma lem3358492 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term128 _87290 f s) = (term129 _87290 f s).
Proof. exact (MK_COMB (@lem3358491 _87290 f s) (@lem3358486 _87290 f s)). Qed.
Lemma lem3358493 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term57 _87290 f s) = (term128 _87290 f s).
Proof. exact (@lem17646 (term34 _87290 s f) (term43 _87290 f s)). Qed.
Lemma lem3358494 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term57 _87290 f s) = (term129 _87290 f s).
Proof. exact (TRANS (@lem3358493 _87290 f s) (@lem3358492 _87290 f s)). Qed.
Lemma lem3358785 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3358786 {_87290 : Type'} (P : Prop) (Q : _87290 -> Prop) : (term130 _87290 P Q) = (term131 _87290 P Q).
Proof. exact (@lem3358785 _87290 P Q). Qed.
Lemma lem3358787 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term132 _87290 f s t) = (term133 _87290 f s t).
Proof. exact (@lem3358786 _87290 (f t) (term98 _87290 s t)). Qed.
Lemma lem3358788 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term134 _87290 s t x) = (term91 _87290 s t x).
Proof. exact (eq_refl (term134 _87290 s t x)). Qed.
Lemma lem3358789 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term135 _87290 s t) = (term98 _87290 s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358788 _87290 s t x)). Qed.
Lemma lem3358790 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358791 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term136 _87290 s t) = (term99 _87290 s t).
Proof. exact (MK_COMB (@lem3358790 _87290) (@lem3358789 _87290 s t)). Qed.
Lemma lem3358792 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term102 _87290 f t) = (term102 _87290 f t).
Proof. exact (eq_refl (term102 _87290 f t)). Qed.
Lemma lem3358793 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term132 _87290 f s t) = (term104 _87290 f s t).
Proof. exact (MK_COMB (@lem3358792 _87290 f t) (@lem3358791 _87290 s t)). Qed.
Lemma lem3358794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358795 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term137 _87290 f s t) = (term138 _87290 f s t).
Proof. exact (MK_COMB (@lem3358794) (@lem3358793 _87290 f s t)). Qed.
Lemma lem3358796 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term134 _87290 s t x) = (term91 _87290 s t x).
Proof. exact (eq_refl (term134 _87290 s t x)). Qed.
Lemma lem3358797 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term102 _87290 f t) = (term102 _87290 f t).
Proof. exact (eq_refl (term102 _87290 f t)). Qed.
Lemma lem3358798 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term139 _87290 f s t x) = (term140 _87290 f s t x).
Proof. exact (MK_COMB (@lem3358797 _87290 f t) (@lem3358796 _87290 s t x)). Qed.
Lemma lem3358799 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term141 _87290 f s t) = (term142 _87290 f s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358798 _87290 f s t x)). Qed.
Lemma lem3358800 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358801 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term133 _87290 f s t) = (term143 _87290 f s t).
Proof. exact (MK_COMB (@lem3358800 _87290) (@lem3358799 _87290 f s t)). Qed.
Lemma lem3358802 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : ((term132 _87290 f s t) = (term133 _87290 f s t)) = ((term104 _87290 f s t) = (term143 _87290 f s t)).
Proof. exact (MK_COMB (@lem3358795 _87290 f s t) (@lem3358801 _87290 f s t)). Qed.
Lemma lem3358803 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term104 _87290 f s t) = (term143 _87290 f s t).
Proof. exact (EQ_MP (@lem3358802 _87290 f s t) (@lem3358787 _87290 f s t)). Qed.
Lemma lem3358804 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term114 _87290 f s) = (term144 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358803 _87290 f s t)). Qed.
Lemma lem3358805 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358806 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term115 _87290 f s) = (term145 _87290 f s).
Proof. exact (MK_COMB (@lem3358805 _87290) (@lem3358804 _87290 f s)). Qed.
Lemma lem3358807 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term123 _87290 s f) = (term123 _87290 s f).
Proof. exact (eq_refl (term123 _87290 s f)). Qed.
Lemma lem3358808 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term125 _87290 f s) = (term146 _87290 f s).
Proof. exact (MK_COMB (@lem3358807 _87290 s f) (@lem3358806 _87290 f s)). Qed.
Lemma lem3358810 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3358811 {_87290 : Type'} (P : Prop) (Q : type686 _87290) : (term147 _87290 P Q) = (term148 _87290 P Q).
Proof. exact (@lem3358810 (_87290 -> Prop) P Q). Qed.
Lemma lem3358812 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term149 _87290 f s) = (term150 _87290 f s).
Proof. exact (@lem3358811 _87290 (term89 _87290 s f) (term144 _87290 f s)). Qed.
Lemma lem3358813 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term151 _87290 f s t) = (term143 _87290 f s t).
Proof. exact (eq_refl (term151 _87290 f s t)). Qed.
Lemma lem3358814 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term152 _87290 f s) = (term144 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358813 _87290 f s t)). Qed.
Lemma lem3358815 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358816 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term153 _87290 f s) = (term145 _87290 f s).
Proof. exact (MK_COMB (@lem3358815 _87290) (@lem3358814 _87290 f s)). Qed.
Lemma lem3358817 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term123 _87290 s f) = (term123 _87290 s f).
Proof. exact (eq_refl (term123 _87290 s f)). Qed.
Lemma lem3358818 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term149 _87290 f s) = (term146 _87290 f s).
Proof. exact (MK_COMB (@lem3358817 _87290 s f) (@lem3358816 _87290 f s)). Qed.
Lemma lem3358819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358820 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term154 _87290 f s) = (term155 _87290 f s).
Proof. exact (MK_COMB (@lem3358819) (@lem3358818 _87290 f s)). Qed.
Lemma lem3358821 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term151 _87290 f s t) = (term143 _87290 f s t).
Proof. exact (eq_refl (term151 _87290 f s t)). Qed.
Lemma lem3358822 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term123 _87290 s f) = (term123 _87290 s f).
Proof. exact (eq_refl (term123 _87290 s f)). Qed.
Lemma lem3358823 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term156 _87290 f s t) = (term157 _87290 f s t).
Proof. exact (MK_COMB (@lem3358822 _87290 s f) (@lem3358821 _87290 f s t)). Qed.
Lemma lem3358824 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term158 _87290 f s) = (term159 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358823 _87290 f s t)). Qed.
Lemma lem3358825 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358826 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term150 _87290 f s) = (term160 _87290 f s).
Proof. exact (MK_COMB (@lem3358825 _87290) (@lem3358824 _87290 f s)). Qed.
Lemma lem3358827 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : ((term149 _87290 f s) = (term150 _87290 f s)) = ((term146 _87290 f s) = (term160 _87290 f s)).
Proof. exact (MK_COMB (@lem3358820 _87290 f s) (@lem3358826 _87290 f s)). Qed.
Lemma lem3358828 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term146 _87290 f s) = (term160 _87290 f s).
Proof. exact (EQ_MP (@lem3358827 _87290 f s) (@lem3358812 _87290 f s)). Qed.
Lemma lem3358830 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3358831 {_87290 : Type'} (P : Prop) (Q : _87290 -> Prop) : (term130 _87290 P Q) = (term131 _87290 P Q).
Proof. exact (@lem3358830 _87290 P Q). Qed.
Lemma lem3358832 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term161 _87290 f s t) = (term162 _87290 f s t).
Proof. exact (@lem3358831 _87290 (term89 _87290 s f) (term142 _87290 f s t)). Qed.
Lemma lem3358833 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term163 _87290 f s t x) = (term140 _87290 f s t x).
Proof. exact (eq_refl (term163 _87290 f s t x)). Qed.
Lemma lem3358834 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term164 _87290 f s t) = (term142 _87290 f s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358833 _87290 f s t x)). Qed.
Lemma lem3358835 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358836 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term165 _87290 f s t) = (term143 _87290 f s t).
Proof. exact (MK_COMB (@lem3358835 _87290) (@lem3358834 _87290 f s t)). Qed.
Lemma lem3358837 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term123 _87290 s f) = (term123 _87290 s f).
Proof. exact (eq_refl (term123 _87290 s f)). Qed.
Lemma lem3358838 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term161 _87290 f s t) = (term157 _87290 f s t).
Proof. exact (MK_COMB (@lem3358837 _87290 s f) (@lem3358836 _87290 f s t)). Qed.
Lemma lem3358839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358840 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term166 _87290 f s t) = (term167 _87290 f s t).
Proof. exact (MK_COMB (@lem3358839) (@lem3358838 _87290 f s t)). Qed.
Lemma lem3358841 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term163 _87290 f s t x) = (term140 _87290 f s t x).
Proof. exact (eq_refl (term163 _87290 f s t x)). Qed.
Lemma lem3358842 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term123 _87290 s f) = (term123 _87290 s f).
Proof. exact (eq_refl (term123 _87290 s f)). Qed.
Lemma lem3358843 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term168 _87290 f s t x) = (term169 _87290 f s t x).
Proof. exact (MK_COMB (@lem3358842 _87290 s f) (@lem3358841 _87290 f s t x)). Qed.
Lemma lem3358844 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term170 _87290 f s t) = (term171 _87290 f s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358843 _87290 f s t x)). Qed.
Lemma lem3358845 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358846 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term162 _87290 f s t) = (term172 _87290 f s t).
Proof. exact (MK_COMB (@lem3358845 _87290) (@lem3358844 _87290 f s t)). Qed.
Lemma lem3358847 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : ((term161 _87290 f s t) = (term162 _87290 f s t)) = ((term157 _87290 f s t) = (term172 _87290 f s t)).
Proof. exact (MK_COMB (@lem3358840 _87290 f s t) (@lem3358846 _87290 f s t)). Qed.
Lemma lem3358848 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term157 _87290 f s t) = (term172 _87290 f s t).
Proof. exact (EQ_MP (@lem3358847 _87290 f s t) (@lem3358832 _87290 f s t)). Qed.
Lemma lem3358849 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term159 _87290 f s) = (term173 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358848 _87290 f s t)). Qed.
Lemma lem3358850 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358851 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term160 _87290 f s) = (term174 _87290 f s).
Proof. exact (MK_COMB (@lem3358850 _87290) (@lem3358849 _87290 f s)). Qed.
Lemma lem3358852 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term146 _87290 f s) = (term174 _87290 f s).
Proof. exact (TRANS (@lem3358828 _87290 f s) (@lem3358851 _87290 f s)). Qed.
Lemma lem3358853 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term125 _87290 f s) = (term174 _87290 f s).
Proof. exact (TRANS (@lem3358808 _87290 f s) (@lem3358852 _87290 f s)). Qed.
Lemma lem3358854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3358855 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term127 _87290 f s) = (term175 _87290 f s).
Proof. exact (MK_COMB (@lem3358854) (@lem3358853 _87290 f s)). Qed.
Lemma lem3358857 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3358858 {_87290 : Type'} (P : Prop) (Q : type686 _87290) : (term147 _87290 P Q) = (term148 _87290 P Q).
Proof. exact (@lem3358857 (_87290 -> Prop) P Q). Qed.
Lemma lem3358859 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term176 _87290 s f x) = (term177 _87290 s f x).
Proof. exact (@lem3358858 _87290 (s x) (term68 _87290 f x)). Qed.
Lemma lem3358860 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term178 _87290 f x t) = (term59 _87290 f t x).
Proof. exact (eq_refl (term178 _87290 f x t)). Qed.
Lemma lem3358861 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term179 _87290 f x) = (term68 _87290 f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358860 _87290 f t x)). Qed.
Lemma lem3358862 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358863 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term180 _87290 f x) = (term69 _87290 f x).
Proof. exact (MK_COMB (@lem3358862 _87290) (@lem3358861 _87290 f x)). Qed.
Lemma lem3358864 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term72 _87290 s x) = (term72 _87290 s x).
Proof. exact (eq_refl (term72 _87290 s x)). Qed.
Lemma lem3358865 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term176 _87290 s f x) = (term74 _87290 s f x).
Proof. exact (MK_COMB (@lem3358864 _87290 s x) (@lem3358863 _87290 f x)). Qed.
Lemma lem3358866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358867 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term181 _87290 s f x) = (term182 _87290 s f x).
Proof. exact (MK_COMB (@lem3358866) (@lem3358865 _87290 s f x)). Qed.
Lemma lem3358868 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term178 _87290 f x t) = (term59 _87290 f t x).
Proof. exact (eq_refl (term178 _87290 f x t)). Qed.
Lemma lem3358869 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term72 _87290 s x) = (term72 _87290 s x).
Proof. exact (eq_refl (term72 _87290 s x)). Qed.
Lemma lem3358870 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term183 _87290 s f x t) = (term184 _87290 s f t x).
Proof. exact (MK_COMB (@lem3358869 _87290 s x) (@lem3358868 _87290 f t x)). Qed.
Lemma lem3358871 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term185 _87290 s f x) = (term186 _87290 s f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358870 _87290 s f t x)). Qed.
Lemma lem3358872 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358873 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term177 _87290 s f x) = (term187 _87290 s f x).
Proof. exact (MK_COMB (@lem3358872 _87290) (@lem3358871 _87290 s f x)). Qed.
Lemma lem3358874 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : ((term176 _87290 s f x) = (term177 _87290 s f x)) = ((term74 _87290 s f x) = (term187 _87290 s f x)).
Proof. exact (MK_COMB (@lem3358867 _87290 s f x) (@lem3358873 _87290 s f x)). Qed.
Lemma lem3358875 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term74 _87290 s f x) = (term187 _87290 s f x).
Proof. exact (EQ_MP (@lem3358874 _87290 s f x) (@lem3358859 _87290 s f x)). Qed.
Lemma lem3358876 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term86 _87290 s f) = (term188 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3358875 _87290 s f x)). Qed.
Lemma lem3358877 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358878 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term87 _87290 s f) = (term189 _87290 s f).
Proof. exact (MK_COMB (@lem3358877 _87290) (@lem3358876 _87290 s f)). Qed.
Lemma lem3358879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3358880 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term119 _87290 s f) = (term190 _87290 s f).
Proof. exact (MK_COMB (@lem3358879) (@lem3358878 _87290 s f)). Qed.
Lemma lem3358881 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term117 _87290 f s) = (term117 _87290 f s).
Proof. exact (eq_refl (term117 _87290 f s)). Qed.
Lemma lem3358882 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term121 _87290 f s) = (term191 _87290 f s).
Proof. exact (MK_COMB (@lem3358880 _87290 s f) (@lem3358881 _87290 f s)). Qed.
Lemma lem3358884 {A : Type'} (P : A -> Prop) (Q : Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3358885 {_87290 : Type'} (P : _87290 -> Prop) (Q : Prop) : (term192 _87290 P Q) = (term193 _87290 P Q).
Proof. exact (@lem3358884 _87290 P Q). Qed.
Lemma lem3358886 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term194 _87290 f s) = (term195 _87290 f s).
Proof. exact (@lem3358885 _87290 (term188 _87290 s f) (term117 _87290 f s)). Qed.
Lemma lem3358887 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term196 _87290 s f x) = (term187 _87290 s f x).
Proof. exact (eq_refl (term196 _87290 s f x)). Qed.
Lemma lem3358888 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term197 _87290 s f) = (term188 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3358887 _87290 s f x)). Qed.
Lemma lem3358889 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358890 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term198 _87290 s f) = (term189 _87290 s f).
Proof. exact (MK_COMB (@lem3358889 _87290) (@lem3358888 _87290 s f)). Qed.
Lemma lem3358891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3358892 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term199 _87290 s f) = (term190 _87290 s f).
Proof. exact (MK_COMB (@lem3358891) (@lem3358890 _87290 s f)). Qed.
Lemma lem3358893 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term117 _87290 f s) = (term117 _87290 f s).
Proof. exact (eq_refl (term117 _87290 f s)). Qed.
Lemma lem3358894 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term194 _87290 f s) = (term191 _87290 f s).
Proof. exact (MK_COMB (@lem3358892 _87290 s f) (@lem3358893 _87290 f s)). Qed.
Lemma lem3358895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358896 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term200 _87290 f s) = (term201 _87290 f s).
Proof. exact (MK_COMB (@lem3358895) (@lem3358894 _87290 f s)). Qed.
Lemma lem3358897 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term196 _87290 s f x) = (term187 _87290 s f x).
Proof. exact (eq_refl (term196 _87290 s f x)). Qed.
Lemma lem3358898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3358899 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term202 _87290 s f x) = (term203 _87290 s f x).
Proof. exact (MK_COMB (@lem3358898) (@lem3358897 _87290 s f x)). Qed.
Lemma lem3358900 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term117 _87290 f s) = (term117 _87290 f s).
Proof. exact (eq_refl (term117 _87290 f s)). Qed.
Lemma lem3358901 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term204 _87290 x f s) = (term205 _87290 x f s).
Proof. exact (MK_COMB (@lem3358899 _87290 s f x) (@lem3358900 _87290 f s)). Qed.
Lemma lem3358902 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term206 _87290 f s) = (term207 _87290 f s).
Proof. exact (fun_ext (fun x : _87290 => @lem3358901 _87290 x f s)). Qed.
Lemma lem3358903 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358904 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term195 _87290 f s) = (term208 _87290 f s).
Proof. exact (MK_COMB (@lem3358903 _87290) (@lem3358902 _87290 f s)). Qed.
Lemma lem3358905 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : ((term194 _87290 f s) = (term195 _87290 f s)) = ((term191 _87290 f s) = (term208 _87290 f s)).
Proof. exact (MK_COMB (@lem3358896 _87290 f s) (@lem3358904 _87290 f s)). Qed.
Lemma lem3358906 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term191 _87290 f s) = (term208 _87290 f s).
Proof. exact (EQ_MP (@lem3358905 _87290 f s) (@lem3358886 _87290 f s)). Qed.
Lemma lem3358908 {A : Type'} (P : A -> Prop) (Q : Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3358909 {_87290 : Type'} (P : type686 _87290) (Q : Prop) : (term209 _87290 P Q) = (term210 _87290 P Q).
Proof. exact (@lem3358908 (_87290 -> Prop) P Q). Qed.
Lemma lem3358910 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term211 _87290 x f s) = (term212 _87290 x f s).
Proof. exact (@lem3358909 _87290 (term186 _87290 s f x) (term117 _87290 f s)). Qed.
Lemma lem3358911 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term213 _87290 s f x t) = (term184 _87290 s f t x).
Proof. exact (eq_refl (term213 _87290 s f x t)). Qed.
Lemma lem3358912 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term214 _87290 s f x) = (term186 _87290 s f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358911 _87290 s f t x)). Qed.
Lemma lem3358913 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358914 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term215 _87290 s f x) = (term187 _87290 s f x).
Proof. exact (MK_COMB (@lem3358913 _87290) (@lem3358912 _87290 s f x)). Qed.
Lemma lem3358915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3358916 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term216 _87290 s f x) = (term203 _87290 s f x).
Proof. exact (MK_COMB (@lem3358915) (@lem3358914 _87290 s f x)). Qed.
Lemma lem3358917 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term117 _87290 f s) = (term117 _87290 f s).
Proof. exact (eq_refl (term117 _87290 f s)). Qed.
Lemma lem3358918 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term211 _87290 x f s) = (term205 _87290 x f s).
Proof. exact (MK_COMB (@lem3358916 _87290 s f x) (@lem3358917 _87290 f s)). Qed.
Lemma lem3358919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358920 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term217 _87290 x f s) = (term218 _87290 x f s).
Proof. exact (MK_COMB (@lem3358919) (@lem3358918 _87290 x f s)). Qed.
Lemma lem3358921 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term213 _87290 s f x t) = (term184 _87290 s f t x).
Proof. exact (eq_refl (term213 _87290 s f x t)). Qed.
Lemma lem3358922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3358923 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term219 _87290 s f x t) = (term220 _87290 s f t x).
Proof. exact (MK_COMB (@lem3358922) (@lem3358921 _87290 s f t x)). Qed.
Lemma lem3358924 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term117 _87290 f s) = (term117 _87290 f s).
Proof. exact (eq_refl (term117 _87290 f s)). Qed.
Lemma lem3358925 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term221 _87290 x t f s) = (term222 _87290 t x f s).
Proof. exact (MK_COMB (@lem3358923 _87290 s f t x) (@lem3358924 _87290 f s)). Qed.
Lemma lem3358926 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term223 _87290 x f s) = (term224 _87290 x f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358925 _87290 t x f s)). Qed.
Lemma lem3358927 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358928 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term212 _87290 x f s) = (term225 _87290 x f s).
Proof. exact (MK_COMB (@lem3358927 _87290) (@lem3358926 _87290 x f s)). Qed.
Lemma lem3358929 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : ((term211 _87290 x f s) = (term212 _87290 x f s)) = ((term205 _87290 x f s) = (term225 _87290 x f s)).
Proof. exact (MK_COMB (@lem3358920 _87290 x f s) (@lem3358928 _87290 x f s)). Qed.
Lemma lem3358930 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term205 _87290 x f s) = (term225 _87290 x f s).
Proof. exact (EQ_MP (@lem3358929 _87290 x f s) (@lem3358910 _87290 x f s)). Qed.
Lemma lem3358931 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term207 _87290 f s) = (term226 _87290 f s).
Proof. exact (fun_ext (fun x : _87290 => @lem3358930 _87290 x f s)). Qed.
Lemma lem3358932 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358933 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term208 _87290 f s) = (term227 _87290 f s).
Proof. exact (MK_COMB (@lem3358932 _87290) (@lem3358931 _87290 f s)). Qed.
Lemma lem3358934 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term191 _87290 f s) = (term227 _87290 f s).
Proof. exact (TRANS (@lem3358906 _87290 f s) (@lem3358933 _87290 f s)). Qed.
Lemma lem3358935 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term121 _87290 f s) = (term227 _87290 f s).
Proof. exact (TRANS (@lem3358882 _87290 f s) (@lem3358934 _87290 f s)). Qed.
Lemma lem3358936 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term129 _87290 f s) = (term228 _87290 f s).
Proof. exact (MK_COMB (@lem3358855 _87290 f s) (@lem3358935 _87290 f s)). Qed.
Lemma lem3358940 {A : Type'} (P : A -> Prop) (Q : Prop) : (term229 A P Q) = (term230 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3358941 {_87290 : Type'} (P : type686 _87290) (Q : Prop) : (term231 _87290 P Q) = (term232 _87290 P Q).
Proof. exact (@lem3358940 (_87290 -> Prop) P Q). Qed.
Lemma lem3358942 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term233 _87290 f s) = (term234 _87290 f s).
Proof. exact (@lem3358941 _87290 (term173 _87290 f s) (term227 _87290 f s)). Qed.
Lemma lem3358943 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term235 _87290 f s t) = (term172 _87290 f s t).
Proof. exact (eq_refl (term235 _87290 f s t)). Qed.
Lemma lem3358944 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term236 _87290 f s) = (term173 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358943 _87290 f s t)). Qed.
Lemma lem3358945 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358946 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term237 _87290 f s) = (term174 _87290 f s).
Proof. exact (MK_COMB (@lem3358945 _87290) (@lem3358944 _87290 f s)). Qed.
Lemma lem3358947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3358948 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term238 _87290 f s) = (term175 _87290 f s).
Proof. exact (MK_COMB (@lem3358947) (@lem3358946 _87290 f s)). Qed.
Lemma lem3358949 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term227 _87290 f s) = (term227 _87290 f s).
Proof. exact (eq_refl (term227 _87290 f s)). Qed.
Lemma lem3358950 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term233 _87290 f s) = (term228 _87290 f s).
Proof. exact (MK_COMB (@lem3358948 _87290 f s) (@lem3358949 _87290 f s)). Qed.
Lemma lem3358951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358952 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term239 _87290 f s) = (term240 _87290 f s).
Proof. exact (MK_COMB (@lem3358951) (@lem3358950 _87290 f s)). Qed.
Lemma lem3358953 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term235 _87290 f s t) = (term172 _87290 f s t).
Proof. exact (eq_refl (term235 _87290 f s t)). Qed.
Lemma lem3358954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3358955 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term241 _87290 f s t) = (term242 _87290 f s t).
Proof. exact (MK_COMB (@lem3358954) (@lem3358953 _87290 f s t)). Qed.
Lemma lem3358956 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term227 _87290 f s) = (term227 _87290 f s).
Proof. exact (eq_refl (term227 _87290 f s)). Qed.
Lemma lem3358957 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term243 _87290 t f s) = (term244 _87290 t f s).
Proof. exact (MK_COMB (@lem3358955 _87290 f s t) (@lem3358956 _87290 f s)). Qed.
Lemma lem3358958 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term245 _87290 f s) = (term246 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358957 _87290 t f s)). Qed.
Lemma lem3358959 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358960 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term234 _87290 f s) = (term247 _87290 f s).
Proof. exact (MK_COMB (@lem3358959 _87290) (@lem3358958 _87290 f s)). Qed.
Lemma lem3358961 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : ((term233 _87290 f s) = (term234 _87290 f s)) = ((term228 _87290 f s) = (term247 _87290 f s)).
Proof. exact (MK_COMB (@lem3358952 _87290 f s) (@lem3358960 _87290 f s)). Qed.
Lemma lem3358962 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term228 _87290 f s) = (term247 _87290 f s).
Proof. exact (EQ_MP (@lem3358961 _87290 f s) (@lem3358942 _87290 f s)). Qed.
Lemma lem3358964 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term248 A P Q) = (term249 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3358965 {_87290 : Type'} (P : _87290 -> Prop) (Q : _87290 -> Prop) : (term248 _87290 P Q) = (term249 _87290 P Q).
Proof. exact (@lem3358964 _87290 P Q). Qed.
Lemma lem3358966 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term250 _87290 t f s) = (term251 _87290 t f s).
Proof. exact (@lem3358965 _87290 (term171 _87290 f s t) (term226 _87290 f s)). Qed.
Lemma lem3358967 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term252 _87290 f s t x) = (term169 _87290 f s t x).
Proof. exact (eq_refl (term252 _87290 f s t x)). Qed.
Lemma lem3358968 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term253 _87290 f s t) = (term171 _87290 f s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3358967 _87290 f s t x)). Qed.
Lemma lem3358969 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358970 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term254 _87290 f s t) = (term172 _87290 f s t).
Proof. exact (MK_COMB (@lem3358969 _87290) (@lem3358968 _87290 f s t)). Qed.
Lemma lem3358971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3358972 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term255 _87290 f s t) = (term242 _87290 f s t).
Proof. exact (MK_COMB (@lem3358971) (@lem3358970 _87290 f s t)). Qed.
Lemma lem3358973 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term256 _87290 f s x) = (term225 _87290 x f s).
Proof. exact (eq_refl (term256 _87290 f s x)). Qed.
Lemma lem3358974 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term257 _87290 f s) = (term226 _87290 f s).
Proof. exact (fun_ext (fun x : _87290 => @lem3358973 _87290 x f s)). Qed.
Lemma lem3358975 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358976 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term258 _87290 f s) = (term227 _87290 f s).
Proof. exact (MK_COMB (@lem3358975 _87290) (@lem3358974 _87290 f s)). Qed.
Lemma lem3358977 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term250 _87290 t f s) = (term244 _87290 t f s).
Proof. exact (MK_COMB (@lem3358972 _87290 f s t) (@lem3358976 _87290 f s)). Qed.
Lemma lem3358978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3358979 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term259 _87290 t f s) = (term260 _87290 t f s).
Proof. exact (MK_COMB (@lem3358978) (@lem3358977 _87290 t f s)). Qed.
Lemma lem3358980 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term252 _87290 f s t x) = (term169 _87290 f s t x).
Proof. exact (eq_refl (term252 _87290 f s t x)). Qed.
Lemma lem3358981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3358982 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term261 _87290 f s t x) = (term262 _87290 f s t x).
Proof. exact (MK_COMB (@lem3358981) (@lem3358980 _87290 f s t x)). Qed.
Lemma lem3358983 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term256 _87290 f s x) = (term225 _87290 x f s).
Proof. exact (eq_refl (term256 _87290 f s x)). Qed.
Lemma lem3358984 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term263 _87290 t f s x) = (term264 _87290 t x f s).
Proof. exact (MK_COMB (@lem3358982 _87290 f s t x) (@lem3358983 _87290 x f s)). Qed.
Lemma lem3358985 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term265 _87290 t f s) = (term266 _87290 t f s).
Proof. exact (fun_ext (fun x : _87290 => @lem3358984 _87290 t x f s)). Qed.
Lemma lem3358986 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3358987 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term251 _87290 t f s) = (term267 _87290 t f s).
Proof. exact (MK_COMB (@lem3358986 _87290) (@lem3358985 _87290 t f s)). Qed.
Lemma lem3358988 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : ((term250 _87290 t f s) = (term251 _87290 t f s)) = ((term244 _87290 t f s) = (term267 _87290 t f s)).
Proof. exact (MK_COMB (@lem3358979 _87290 t f s) (@lem3358987 _87290 t f s)). Qed.
Lemma lem3358989 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term244 _87290 t f s) = (term267 _87290 t f s).
Proof. exact (EQ_MP (@lem3358988 _87290 t f s) (@lem3358966 _87290 t f s)). Qed.
Lemma lem3358991 {A : Type'} (P : Prop) (Q : A -> Prop) : (term268 A P Q) = (term269 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3358992 {_87290 : Type'} (P : Prop) (Q : type686 _87290) : (term270 _87290 P Q) = (term271 _87290 P Q).
Proof. exact (@lem3358991 (_87290 -> Prop) P Q). Qed.
Lemma lem3358993 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term272 _87290 t x f s) = (term273 _87290 t x f s).
Proof. exact (@lem3358992 _87290 (term169 _87290 f s t x) (term224 _87290 x f s)). Qed.
Lemma lem3358994 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term274 _87290 x f s t) = (term222 _87290 t x f s).
Proof. exact (eq_refl (term274 _87290 x f s t)). Qed.
Lemma lem3358995 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term275 _87290 x f s) = (term224 _87290 x f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3358994 _87290 t x f s)). Qed.
Lemma lem3358996 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3358997 {_87290 : Type'} (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term276 _87290 x f s) = (term225 _87290 x f s).
Proof. exact (MK_COMB (@lem3358996 _87290) (@lem3358995 _87290 x f s)). Qed.
Lemma lem3358998 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term262 _87290 f s t x) = (term262 _87290 f s t x).
Proof. exact (eq_refl (term262 _87290 f s t x)). Qed.
Lemma lem3358999 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term272 _87290 t x f s) = (term264 _87290 t x f s).
Proof. exact (MK_COMB (@lem3358998 _87290 f s t x) (@lem3358997 _87290 x f s)). Qed.
Lemma lem3359000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3359001 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term277 _87290 t x f s) = (term278 _87290 t x f s).
Proof. exact (MK_COMB (@lem3359000) (@lem3358999 _87290 t x f s)). Qed.
Lemma lem3359002 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term274 _87290 x f s t') = (term222 _87290 t' x f s).
Proof. exact (eq_refl (term274 _87290 x f s t')). Qed.
Lemma lem3359003 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term262 _87290 f s t x) = (term262 _87290 f s t x).
Proof. exact (eq_refl (term262 _87290 f s t x)). Qed.
Lemma lem3359004 {_87290 : Type'} (t : _87290 -> Prop) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term279 _87290 t x f s t') = (term280 _87290 t t' x f s).
Proof. exact (MK_COMB (@lem3359003 _87290 f s t x) (@lem3359002 _87290 t' x f s)). Qed.
Lemma lem3359005 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term281 _87290 t x f s) = (term282 _87290 t x f s).
Proof. exact (fun_ext (fun t' : _87290 -> Prop => @lem3359004 _87290 t t' x f s)). Qed.
Lemma lem3359006 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3359007 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term273 _87290 t x f s) = (term283 _87290 t x f s).
Proof. exact (MK_COMB (@lem3359006 _87290) (@lem3359005 _87290 t x f s)). Qed.
Lemma lem3359008 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : ((term272 _87290 t x f s) = (term273 _87290 t x f s)) = ((term264 _87290 t x f s) = (term283 _87290 t x f s)).
Proof. exact (MK_COMB (@lem3359001 _87290 t x f s) (@lem3359007 _87290 t x f s)). Qed.
Lemma lem3359009 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term264 _87290 t x f s) = (term283 _87290 t x f s).
Proof. exact (EQ_MP (@lem3359008 _87290 t x f s) (@lem3358993 _87290 t x f s)). Qed.
Lemma lem3359010 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term266 _87290 t f s) = (term284 _87290 t f s).
Proof. exact (fun_ext (fun x : _87290 => @lem3359009 _87290 t x f s)). Qed.
Lemma lem3359011 {_87290 : Type'} : (@ex _87290) = (@ex _87290).
Proof. exact (eq_refl (@ex _87290)). Qed.
Lemma lem3359012 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term267 _87290 t f s) = (term285 _87290 t f s).
Proof. exact (MK_COMB (@lem3359011 _87290) (@lem3359010 _87290 t f s)). Qed.
Lemma lem3359013 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) : (term244 _87290 t f s) = (term285 _87290 t f s).
Proof. exact (TRANS (@lem3358989 _87290 t f s) (@lem3359012 _87290 t f s)). Qed.
Lemma lem3359014 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term246 _87290 f s) = (term286 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359013 _87290 t f s)). Qed.
Lemma lem3359015 {_87290 : Type'} : (@ex (_87290 -> Prop)) = (@ex (_87290 -> Prop)).
Proof. exact (eq_refl (@ex (_87290 -> Prop))). Qed.
Lemma lem3359016 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term247 _87290 f s) = (term287 _87290 f s).
Proof. exact (MK_COMB (@lem3359015 _87290) (@lem3359014 _87290 f s)). Qed.
Lemma lem3359017 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term228 _87290 f s) = (term287 _87290 f s).
Proof. exact (TRANS (@lem3358962 _87290 f s) (@lem3359016 _87290 f s)). Qed.
Lemma lem3359019 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term129 _87290 f s) = (term287 _87290 f s).
Proof. exact (TRANS (@lem3358936 _87290 f s) (@lem3359017 _87290 f s)). Qed.
Lemma lem3359020 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term57 _87290 f s) = (term287 _87290 f s).
Proof. exact (TRANS (@lem3358494 _87290 f s) (@lem3359019 _87290 f s)). Qed.
Lemma lem3359021 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (h1 : term57 _87290 f s) : term287 _87290 f s.
Proof. exact (EQ_MP (@lem3359020 _87290 f s) (@lem3358379 _87290 f s h1)). Qed.
Lemma lem3359022 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term285 _87290 t f s) : term285 _87290 t f s.
Proof. exact (h1). Qed.
Lemma lem3359023 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term283 _87290 t x f s) : term283 _87290 t x f s.
Proof. exact (h1). Qed.
Lemma lem3359024 {_87290 : Type'} (t : _87290 -> Prop) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term280 _87290 t t' x f s) : term280 _87290 t t' x f s.
Proof. exact (h1). Qed.
Lemma lem3359029 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359030 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359029 _87290 Prop f x). Qed.
Lemma lem3359032 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (t x) = (@I (_87290 -> Prop) t x).
Proof. exact (@lem3359030 _87290 t x). Qed.
Lemma lem3359033 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359039 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359038 _87290 Prop f x). Qed.
Lemma lem3359041 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (s x) = (@I (_87290 -> Prop) s x).
Proof. exact (@lem3359039 _87290 s x). Qed.
Lemma lem3359042 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term288 _87290 s x) = (term289 _87290 s x).
Proof. exact (MK_COMB (@lem3359033) (@lem3359041 _87290 s x)). Qed.
Lemma lem3359043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3359044 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term76 _87290 s x) = (term290 _87290 s x).
Proof. exact (MK_COMB (@lem3359043) (@lem3359042 _87290 s x)). Qed.
Lemma lem3359045 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term92 _87290 s t x) = (term291 _87290 s t x).
Proof. exact (MK_COMB (@lem3359044 _87290 s x) (@lem3359032 _87290 t x)). Qed.
Lemma lem3359046 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term100 _87290 s t) = (term292 _87290 s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3359045 _87290 s t x)). Qed.
Lemma lem3359047 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3359048 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term101 _87290 s t) = (term293 _87290 s t).
Proof. exact (MK_COMB (@lem3359047 _87290) (@lem3359046 _87290 s t)). Qed.
Lemma lem3359049 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359054 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359055 {_87290 : Type'} (f : type686 _87290) (x : _87290 -> Prop) : (f x) = (@I ((_87290 -> Prop) -> Prop) f x).
Proof. exact (@lem3359054 (_87290 -> Prop) Prop f x). Qed.
Lemma lem3359057 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (f t) = (@I ((_87290 -> Prop) -> Prop) f t).
Proof. exact (@lem3359055 _87290 f t). Qed.
Lemma lem3359058 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term294 _87290 f t) = (term295 _87290 f t).
Proof. exact (MK_COMB (@lem3359049) (@lem3359057 _87290 f t)). Qed.
Lemma lem3359059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3359060 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term106 _87290 f t) = (term296 _87290 f t).
Proof. exact (MK_COMB (@lem3359059) (@lem3359058 _87290 f t)). Qed.
Lemma lem3359061 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term108 _87290 f s t) = (term297 _87290 f s t).
Proof. exact (MK_COMB (@lem3359060 _87290 f t) (@lem3359048 _87290 s t)). Qed.
Lemma lem3359062 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term116 _87290 f s) = (term298 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359061 _87290 f s t)). Qed.
Lemma lem3359063 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3359064 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term117 _87290 f s) = (term299 _87290 f s).
Proof. exact (MK_COMB (@lem3359063 _87290) (@lem3359062 _87290 f s)). Qed.
Lemma lem3359065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359070 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359071 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359070 _87290 Prop f x). Qed.
Lemma lem3359073 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) : (t' x) = (@I (_87290 -> Prop) t' x).
Proof. exact (@lem3359071 _87290 t' x). Qed.
Lemma lem3359074 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) : (term288 _87290 t' x) = (term289 _87290 t' x).
Proof. exact (MK_COMB (@lem3359065) (@lem3359073 _87290 t' x)). Qed.
Lemma lem3359079 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359080 {_87290 : Type'} (f : type686 _87290) (x : _87290 -> Prop) : (f x) = (@I ((_87290 -> Prop) -> Prop) f x).
Proof. exact (@lem3359079 (_87290 -> Prop) Prop f x). Qed.
Lemma lem3359082 {_87290 : Type'} (f : type686 _87290) (t' : _87290 -> Prop) : (f t') = (@I ((_87290 -> Prop) -> Prop) f t').
Proof. exact (@lem3359080 _87290 f t'). Qed.
Lemma lem3359083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359084 {_87290 : Type'} (f : type686 _87290) (t' : _87290 -> Prop) : (term102 _87290 f t') = (term300 _87290 f t').
Proof. exact (MK_COMB (@lem3359083) (@lem3359082 _87290 f t')). Qed.
Lemma lem3359085 {_87290 : Type'} (f : type686 _87290) (t' : _87290 -> Prop) (x : _87290) : (term59 _87290 f t' x) = (term301 _87290 f t' x).
Proof. exact (MK_COMB (@lem3359084 _87290 f t') (@lem3359074 _87290 t' x)). Qed.
Lemma lem3359090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359091 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359090 _87290 Prop f x). Qed.
Lemma lem3359093 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (s x) = (@I (_87290 -> Prop) s x).
Proof. exact (@lem3359091 _87290 s x). Qed.
Lemma lem3359094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359095 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term72 _87290 s x) = (term302 _87290 s x).
Proof. exact (MK_COMB (@lem3359094) (@lem3359093 _87290 s x)). Qed.
Lemma lem3359096 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t' : _87290 -> Prop) (x : _87290) : (term184 _87290 s f t' x) = (term303 _87290 s f t' x).
Proof. exact (MK_COMB (@lem3359095 _87290 s x) (@lem3359085 _87290 f t' x)). Qed.
Lemma lem3359097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359098 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t' : _87290 -> Prop) (x : _87290) : (term220 _87290 s f t' x) = (term304 _87290 s f t' x).
Proof. exact (MK_COMB (@lem3359097) (@lem3359096 _87290 s f t' x)). Qed.
Lemma lem3359099 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term222 _87290 t' x f s) = (term305 _87290 t' x f s).
Proof. exact (MK_COMB (@lem3359098 _87290 s f t' x) (@lem3359064 _87290 f s)). Qed.
Lemma lem3359100 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359106 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359105 _87290 Prop f x). Qed.
Lemma lem3359108 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (t x) = (@I (_87290 -> Prop) t x).
Proof. exact (@lem3359106 _87290 t x). Qed.
Lemma lem3359109 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (term288 _87290 t x) = (term289 _87290 t x).
Proof. exact (MK_COMB (@lem3359100) (@lem3359108 _87290 t x)). Qed.
Lemma lem3359114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359115 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359114 _87290 Prop f x). Qed.
Lemma lem3359117 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (s x) = (@I (_87290 -> Prop) s x).
Proof. exact (@lem3359115 _87290 s x). Qed.
Lemma lem3359118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359119 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term72 _87290 s x) = (term302 _87290 s x).
Proof. exact (MK_COMB (@lem3359118) (@lem3359117 _87290 s x)). Qed.
Lemma lem3359120 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term91 _87290 s t x) = (term306 _87290 s t x).
Proof. exact (MK_COMB (@lem3359119 _87290 s x) (@lem3359109 _87290 t x)). Qed.
Lemma lem3359125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359126 {_87290 : Type'} (f : type686 _87290) (x : _87290 -> Prop) : (f x) = (@I ((_87290 -> Prop) -> Prop) f x).
Proof. exact (@lem3359125 (_87290 -> Prop) Prop f x). Qed.
Lemma lem3359128 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (f t) = (@I ((_87290 -> Prop) -> Prop) f t).
Proof. exact (@lem3359126 _87290 f t). Qed.
Lemma lem3359129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359130 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term102 _87290 f t) = (term300 _87290 f t).
Proof. exact (MK_COMB (@lem3359129) (@lem3359128 _87290 f t)). Qed.
Lemma lem3359131 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term140 _87290 f s t x) = (term307 _87290 f s t x).
Proof. exact (MK_COMB (@lem3359130 _87290 f t) (@lem3359120 _87290 s t x)). Qed.
Lemma lem3359136 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359137 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359136 _87290 Prop f x). Qed.
Lemma lem3359139 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (t x) = (@I (_87290 -> Prop) t x).
Proof. exact (@lem3359137 _87290 t x). Qed.
Lemma lem3359140 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359145 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359146 {_87290 : Type'} (f : type686 _87290) (x : _87290 -> Prop) : (f x) = (@I ((_87290 -> Prop) -> Prop) f x).
Proof. exact (@lem3359145 (_87290 -> Prop) Prop f x). Qed.
Lemma lem3359148 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (f t) = (@I ((_87290 -> Prop) -> Prop) f t).
Proof. exact (@lem3359146 _87290 f t). Qed.
Lemma lem3359149 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term294 _87290 f t) = (term295 _87290 f t).
Proof. exact (MK_COMB (@lem3359140) (@lem3359148 _87290 f t)). Qed.
Lemma lem3359150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3359151 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term106 _87290 f t) = (term296 _87290 f t).
Proof. exact (MK_COMB (@lem3359150) (@lem3359149 _87290 f t)). Qed.
Lemma lem3359152 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term60 _87290 f t x) = (term308 _87290 f t x).
Proof. exact (MK_COMB (@lem3359151 _87290 f t) (@lem3359139 _87290 t x)). Qed.
Lemma lem3359153 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term70 _87290 f x) = (term309 _87290 f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359152 _87290 f t x)). Qed.
Lemma lem3359154 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3359155 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term71 _87290 f x) = (term310 _87290 f x).
Proof. exact (MK_COMB (@lem3359154 _87290) (@lem3359153 _87290 f x)). Qed.
Lemma lem3359156 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3359161 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3359162 {_87290 : Type'} (f : _87290 -> Prop) (x : _87290) : (f x) = (@I (_87290 -> Prop) f x).
Proof. exact (@lem3359161 _87290 Prop f x). Qed.
Lemma lem3359164 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (s x) = (@I (_87290 -> Prop) s x).
Proof. exact (@lem3359162 _87290 s x). Qed.
Lemma lem3359165 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term288 _87290 s x) = (term289 _87290 s x).
Proof. exact (MK_COMB (@lem3359156) (@lem3359164 _87290 s x)). Qed.
Lemma lem3359166 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3359167 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term76 _87290 s x) = (term290 _87290 s x).
Proof. exact (MK_COMB (@lem3359166) (@lem3359165 _87290 s x)). Qed.
Lemma lem3359168 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term78 _87290 s f x) = (term311 _87290 s f x).
Proof. exact (MK_COMB (@lem3359167 _87290 s x) (@lem3359155 _87290 f x)). Qed.
Lemma lem3359169 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term88 _87290 s f) = (term312 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3359168 _87290 s f x)). Qed.
Lemma lem3359170 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3359171 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term89 _87290 s f) = (term313 _87290 s f).
Proof. exact (MK_COMB (@lem3359170 _87290) (@lem3359169 _87290 s f)). Qed.
Lemma lem3359172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359173 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term123 _87290 s f) = (term314 _87290 s f).
Proof. exact (MK_COMB (@lem3359172) (@lem3359171 _87290 s f)). Qed.
Lemma lem3359174 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term169 _87290 f s t x) = (term315 _87290 f s t x).
Proof. exact (MK_COMB (@lem3359173 _87290 s f) (@lem3359131 _87290 f s t x)). Qed.
Lemma lem3359175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3359176 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term262 _87290 f s t x) = (term316 _87290 f s t x).
Proof. exact (MK_COMB (@lem3359175) (@lem3359174 _87290 f s t x)). Qed.
Lemma lem3359177 {_87290 : Type'} (t : _87290 -> Prop) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) : (term280 _87290 t t' x f s) = (term317 _87290 t t' x f s).
Proof. exact (MK_COMB (@lem3359176 _87290 f s t x) (@lem3359099 _87290 t' x f s)). Qed.
Lemma lem3359178 {_87290 : Type'} (t : _87290 -> Prop) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term280 _87290 t t' x f s) : term317 _87290 t t' x f s.
Proof. exact (EQ_MP (@lem3359177 _87290 t t' x f s) (@lem3359024 _87290 t t' x f s h1)). Qed.
Lemma lem3359179 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term315 _87290 f s t x.
Proof. exact (h1). Qed.
Lemma lem3359180 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term305 _87290 t' x f s.
Proof. exact (h1). Qed.
Lemma lem3359181 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term307 _87290 f s t x.
Proof. exact (proj2 (@lem3359179 _87290 f s t x h1)). Qed.
Lemma lem3359182 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term313 _87290 s f.
Proof. exact (proj1 (@lem3359179 _87290 f s t x h1)). Qed.
Lemma lem3359183 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term306 _87290 s t x.
Proof. exact (proj2 (@lem3359181 _87290 f s t x h1)). Qed.
Lemma lem3359187 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term299 _87290 f s.
Proof. exact (proj2 (@lem3359180 _87290 t' x f s h1)). Qed.
Lemma lem3359188 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term303 _87290 s f t' x.
Proof. exact (proj1 (@lem3359180 _87290 t' x f s h1)). Qed.
Lemma lem3359189 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term301 _87290 f t' x.
Proof. exact (proj2 (@lem3359188 _87290 t' x f s h1)). Qed.
Lemma lem3359194 {A : Type'} (P : Prop) (Q : A -> Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3359195 {_87290 : Type'} (P : Prop) (Q : type686 _87290) : (term320 _87290 P Q) = (term321 _87290 P Q).
Proof. exact (@lem3359194 (_87290 -> Prop) P Q). Qed.
Lemma lem3359196 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term322 _87290 s f x) = (term323 _87290 s f x).
Proof. exact (@lem3359195 _87290 (term289 _87290 s x) (term309 _87290 f x)). Qed.
Lemma lem3359197 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term324 _87290 f x t) = (term308 _87290 f t x).
Proof. exact (eq_refl (term324 _87290 f x t)). Qed.
Lemma lem3359198 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term325 _87290 f x) = (term309 _87290 f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359197 _87290 f t x)). Qed.
Lemma lem3359199 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3359200 {_87290 : Type'} (f : type686 _87290) (x : _87290) : (term326 _87290 f x) = (term310 _87290 f x).
Proof. exact (MK_COMB (@lem3359199 _87290) (@lem3359198 _87290 f x)). Qed.
Lemma lem3359201 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term290 _87290 s x) = (term290 _87290 s x).
Proof. exact (eq_refl (term290 _87290 s x)). Qed.
Lemma lem3359202 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term322 _87290 s f x) = (term311 _87290 s f x).
Proof. exact (MK_COMB (@lem3359201 _87290 s x) (@lem3359200 _87290 f x)). Qed.
Lemma lem3359203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3359204 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term327 _87290 s f x) = (term328 _87290 s f x).
Proof. exact (MK_COMB (@lem3359203) (@lem3359202 _87290 s f x)). Qed.
Lemma lem3359205 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term324 _87290 f x t) = (term308 _87290 f t x).
Proof. exact (eq_refl (term324 _87290 f x t)). Qed.
Lemma lem3359206 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term290 _87290 s x) = (term290 _87290 s x).
Proof. exact (eq_refl (term290 _87290 s x)). Qed.
Lemma lem3359207 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term329 _87290 s f x t) = (term330 _87290 s f t x).
Proof. exact (MK_COMB (@lem3359206 _87290 s x) (@lem3359205 _87290 f t x)). Qed.
Lemma lem3359208 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term331 _87290 s f x) = (term332 _87290 s f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359207 _87290 s f t x)). Qed.
Lemma lem3359209 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3359210 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term323 _87290 s f x) = (term333 _87290 s f x).
Proof. exact (MK_COMB (@lem3359209 _87290) (@lem3359208 _87290 s f x)). Qed.
Lemma lem3359211 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : ((term322 _87290 s f x) = (term323 _87290 s f x)) = ((term311 _87290 s f x) = (term333 _87290 s f x)).
Proof. exact (MK_COMB (@lem3359204 _87290 s f x) (@lem3359210 _87290 s f x)). Qed.
Lemma lem3359212 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term311 _87290 s f x) = (term333 _87290 s f x).
Proof. exact (EQ_MP (@lem3359211 _87290 s f x) (@lem3359196 _87290 s f x)). Qed.
Lemma lem3359213 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term312 _87290 s f) = (term334 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3359212 _87290 s f x)). Qed.
Lemma lem3359214 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3359215 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term313 _87290 s f) = (term335 _87290 s f).
Proof. exact (MK_COMB (@lem3359214 _87290) (@lem3359213 _87290 s f)). Qed.
Lemma lem3359228 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (t : _87290 -> Prop) (x : _87290) : (term330 _87290 s f t x) = (term330 _87290 s f t x).
Proof. exact (eq_refl (term330 _87290 s f t x)). Qed.
Lemma lem3359229 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term332 _87290 s f x) = (term332 _87290 s f x).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359228 _87290 s f t x)). Qed.
Lemma lem3359230 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3359231 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (x : _87290) : (term333 _87290 s f x) = (term333 _87290 s f x).
Proof. exact (MK_COMB (@lem3359230 _87290) (@lem3359229 _87290 s f x)). Qed.
Lemma lem3359232 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term334 _87290 s f) = (term334 _87290 s f).
Proof. exact (fun_ext (fun x : _87290 => @lem3359231 _87290 s f x)). Qed.
Lemma lem3359233 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3359234 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term335 _87290 s f) = (term335 _87290 s f).
Proof. exact (MK_COMB (@lem3359233 _87290) (@lem3359232 _87290 s f)). Qed.
Lemma lem3359235 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) : (term313 _87290 s f) = (term335 _87290 s f).
Proof. exact (TRANS (@lem3359215 _87290 s f) (@lem3359234 _87290 s f)). Qed.
Lemma lem3359236 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term335 _87290 s f.
Proof. exact (EQ_MP (@lem3359235 _87290 s f) (@lem3359182 _87290 f s t x h1)). Qed.
Lemma lem3359250 {A : Type'} (P : Prop) (Q : A -> Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3359251 {_87290 : Type'} (P : Prop) (Q : _87290 -> Prop) : (term318 _87290 P Q) = (term319 _87290 P Q).
Proof. exact (@lem3359250 _87290 P Q). Qed.
Lemma lem3359252 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term336 _87290 f s t) = (term337 _87290 f s t).
Proof. exact (@lem3359251 _87290 (term295 _87290 f t) (term292 _87290 s t)). Qed.
Lemma lem3359253 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term338 _87290 s t x) = (term291 _87290 s t x).
Proof. exact (eq_refl (term338 _87290 s t x)). Qed.
Lemma lem3359254 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term339 _87290 s t) = (term292 _87290 s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3359253 _87290 s t x)). Qed.
Lemma lem3359255 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3359256 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) : (term340 _87290 s t) = (term293 _87290 s t).
Proof. exact (MK_COMB (@lem3359255 _87290) (@lem3359254 _87290 s t)). Qed.
Lemma lem3359257 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term296 _87290 f t) = (term296 _87290 f t).
Proof. exact (eq_refl (term296 _87290 f t)). Qed.
Lemma lem3359258 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term336 _87290 f s t) = (term297 _87290 f s t).
Proof. exact (MK_COMB (@lem3359257 _87290 f t) (@lem3359256 _87290 s t)). Qed.
Lemma lem3359259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3359260 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term341 _87290 f s t) = (term342 _87290 f s t).
Proof. exact (MK_COMB (@lem3359259) (@lem3359258 _87290 f s t)). Qed.
Lemma lem3359261 {_87290 : Type'} (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term338 _87290 s t x) = (term291 _87290 s t x).
Proof. exact (eq_refl (term338 _87290 s t x)). Qed.
Lemma lem3359262 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term296 _87290 f t) = (term296 _87290 f t).
Proof. exact (eq_refl (term296 _87290 f t)). Qed.
Lemma lem3359263 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term343 _87290 f s t x) = (term344 _87290 f s t x).
Proof. exact (MK_COMB (@lem3359262 _87290 f t) (@lem3359261 _87290 s t x)). Qed.
Lemma lem3359264 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term345 _87290 f s t) = (term346 _87290 f s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3359263 _87290 f s t x)). Qed.
Lemma lem3359265 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3359266 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term337 _87290 f s t) = (term347 _87290 f s t).
Proof. exact (MK_COMB (@lem3359265 _87290) (@lem3359264 _87290 f s t)). Qed.
Lemma lem3359267 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : ((term336 _87290 f s t) = (term337 _87290 f s t)) = ((term297 _87290 f s t) = (term347 _87290 f s t)).
Proof. exact (MK_COMB (@lem3359260 _87290 f s t) (@lem3359266 _87290 f s t)). Qed.
Lemma lem3359268 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term297 _87290 f s t) = (term347 _87290 f s t).
Proof. exact (EQ_MP (@lem3359267 _87290 f s t) (@lem3359252 _87290 f s t)). Qed.
Lemma lem3359269 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term298 _87290 f s) = (term348 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359268 _87290 f s t)). Qed.
Lemma lem3359270 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3359271 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term299 _87290 f s) = (term349 _87290 f s).
Proof. exact (MK_COMB (@lem3359270 _87290) (@lem3359269 _87290 f s)). Qed.
Lemma lem3359284 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) : (term344 _87290 f s t x) = (term344 _87290 f s t x).
Proof. exact (eq_refl (term344 _87290 f s t x)). Qed.
Lemma lem3359285 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term346 _87290 f s t) = (term346 _87290 f s t).
Proof. exact (fun_ext (fun x : _87290 => @lem3359284 _87290 f s t x)). Qed.
Lemma lem3359286 {_87290 : Type'} : (@all _87290) = (@all _87290).
Proof. exact (eq_refl (@all _87290)). Qed.
Lemma lem3359287 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) : (term347 _87290 f s t) = (term347 _87290 f s t).
Proof. exact (MK_COMB (@lem3359286 _87290) (@lem3359285 _87290 f s t)). Qed.
Lemma lem3359288 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term348 _87290 f s) = (term348 _87290 f s).
Proof. exact (fun_ext (fun t : _87290 -> Prop => @lem3359287 _87290 f s t)). Qed.
Lemma lem3359289 {_87290 : Type'} : (@all (_87290 -> Prop)) = (@all (_87290 -> Prop)).
Proof. exact (eq_refl (@all (_87290 -> Prop))). Qed.
Lemma lem3359290 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term349 _87290 f s) = (term349 _87290 f s).
Proof. exact (MK_COMB (@lem3359289 _87290) (@lem3359288 _87290 f s)). Qed.
Lemma lem3359291 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term299 _87290 f s) = (term349 _87290 f s).
Proof. exact (TRANS (@lem3359271 _87290 f s) (@lem3359290 _87290 f s)). Qed.
Lemma lem3359292 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term349 _87290 f s.
Proof. exact (EQ_MP (@lem3359291 _87290 f s) (@lem3359187 _87290 t' x f s h1)). Qed.
Lemma lem3359305 {_87290 : Type'} (_35061 : _87290) (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term350 _87290 s f _35061.
Proof. exact (@lem3359236 _87290 f s t x h1 _35061). Qed.
Lemma lem3359306 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (_35061 : _87290) : (term350 _87290 s f _35061) = (term333 _87290 s f _35061).
Proof. exact (eq_refl (term350 _87290 s f _35061)). Qed.
Lemma lem3359307 {_87290 : Type'} (_35061 : _87290) (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term333 _87290 s f _35061.
Proof. exact (EQ_MP (@lem3359306 _87290 s f _35061) (@lem3359305 _87290 _35061 f s t x h1)). Qed.
Lemma lem3359308 {_87290 : Type'} (_35061 : _87290) (_35062 : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term351 _87290 s f _35061 _35062.
Proof. exact (@lem3359307 _87290 _35061 f s t x h1 _35062). Qed.
Lemma lem3359309 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (_35062 : _87290 -> Prop) (_35061 : _87290) : (term351 _87290 s f _35061 _35062) = (term330 _87290 s f _35062 _35061).
Proof. exact (eq_refl (term351 _87290 s f _35061 _35062)). Qed.
Lemma lem3359311 {_87290 : Type'} (_35063 : _87290 -> Prop) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term352 _87290 f s _35063.
Proof. exact (@lem3359292 _87290 t' x f s h1 _35063). Qed.
Lemma lem3359312 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (_35063 : _87290 -> Prop) : (term352 _87290 f s _35063) = (term347 _87290 f s _35063).
Proof. exact (eq_refl (term352 _87290 f s _35063)). Qed.
Lemma lem3359313 {_87290 : Type'} (_35063 : _87290 -> Prop) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term347 _87290 f s _35063.
Proof. exact (EQ_MP (@lem3359312 _87290 f s _35063) (@lem3359311 _87290 _35063 t' x f s h1)). Qed.
Lemma lem3359314 {_87290 : Type'} (_35063 : _87290 -> Prop) (_35064 : _87290) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term353 _87290 f s _35063 _35064.
Proof. exact (@lem3359313 _87290 _35063 t' x f s h1 _35064). Qed.
Lemma lem3359315 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (_35063 : _87290 -> Prop) (_35064 : _87290) : (term353 _87290 f s _35063 _35064) = (term344 _87290 f s _35063 _35064).
Proof. exact (eq_refl (term353 _87290 f s _35063 _35064)). Qed.
Lemma lem3359326 {_87290 : Type'} (_35062 : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term330 _87290 s f _35062 _35061.
Proof. exact (EQ_MP (@lem3359309 _87290 s f _35062 _35061) (@lem3359308 _87290 _35061 _35062 f s t x h1)). Qed.
Lemma lem3359332 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term289 _87290 t x.
Proof. exact (proj2 (@lem3359183 _87290 f s t x h1)). Qed.
Lemma lem3359342 {_87290 : Type'} (_35063 : _87290 -> Prop) (_35064 : _87290) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term344 _87290 f s _35063 _35064.
Proof. exact (EQ_MP (@lem3359315 _87290 f s _35063 _35064) (@lem3359314 _87290 _35063 _35064 t' x f s h1)). Qed.
Lemma lem3359348 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term289 _87290 t' x.
Proof. exact (proj2 (@lem3359189 _87290 t' x f s h1)). Qed.
Lemma lem3359350 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : @I (_87290 -> Prop) s x.
Proof. exact (proj1 (@lem3359183 _87290 f s t x h1)). Qed.
Lemma lem3359351 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term354 _87290 s x.
Proof. exact (fun h0 : term289 _87290 s x => @lem3359350 _87290 f s t x h1). Qed.
Lemma lem3359353 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359354 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term354 _87290 s x) = (@I (_87290 -> Prop) s x).
Proof. exact (@lem3359353 (@I (_87290 -> Prop) s x)). Qed.
Lemma lem3359355 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : @I (_87290 -> Prop) s x.
Proof. exact (EQ_MP (@lem3359354 _87290 s x) (@lem3359351 _87290 f s t x h1)). Qed.
Lemma lem3359357 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : @I ((_87290 -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3359181 _87290 f s t x h1)). Qed.
Lemma lem3359358 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term356 _87290 f t.
Proof. exact (fun h0 : term295 _87290 f t => @lem3359357 _87290 f s t x h1). Qed.
Lemma lem3359360 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359361 {_87290 : Type'} (f : type686 _87290) (t : _87290 -> Prop) : (term356 _87290 f t) = (@I ((_87290 -> Prop) -> Prop) f t).
Proof. exact (@lem3359360 (@I ((_87290 -> Prop) -> Prop) f t)). Qed.
Lemma lem3359362 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : @I ((_87290 -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3359361 _87290 f t) (@lem3359358 _87290 f s t x h1)). Qed.
Lemma lem3359378 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3359379 {_87290 : Type'} (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term308 _87290 f _35062 _35061) = (term357 _87290 _35061 f _35062).
Proof. exact (@lem3359378 (@I (_87290 -> Prop) _35062 _35061) (term295 _87290 f _35062)). Qed.
Lemma lem3359385 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) : (term290 _87290 s _35061) = (term290 _87290 s _35061).
Proof. exact (eq_refl (term290 _87290 s _35061)). Qed.
Lemma lem3359386 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term330 _87290 s f _35062 _35061) = (term358 _87290 s _35061 f _35062).
Proof. exact (MK_COMB (@lem3359385 _87290 s _35061) (@lem3359379 _87290 _35061 f _35062)). Qed.
Lemma lem3359390 (q : Prop) (p : Prop) (r : Prop) : (term359 p q r) = (term359 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3359391 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term358 _87290 s _35061 f _35062) = (term360 _87290 s _35061 f _35062).
Proof. exact (@lem3359390 (@I (_87290 -> Prop) _35062 _35061) (term289 _87290 s _35061) (term295 _87290 f _35062)). Qed.
Lemma lem3359407 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term330 _87290 s f _35062 _35061) = (term360 _87290 s _35061 f _35062).
Proof. exact (TRANS (@lem3359386 _87290 s _35061 f _35062) (@lem3359391 _87290 s _35061 f _35062)). Qed.
Lemma lem3359408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3359409 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term361 _87290 s f _35062 _35061) = (term362 _87290 s _35061 f _35062).
Proof. exact (MK_COMB (@lem3359408) (@lem3359407 _87290 s _35061 f _35062)). Qed.
Lemma lem3359425 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term360 _87290 s _35061 f _35062) = (term360 _87290 s _35061 f _35062).
Proof. exact (eq_refl (term360 _87290 s _35061 f _35062)). Qed.
Lemma lem3359426 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : ((term330 _87290 s f _35062 _35061) = (term360 _87290 s _35061 f _35062)) = ((term360 _87290 s _35061 f _35062) = (term360 _87290 s _35061 f _35062)).
Proof. exact (MK_COMB (@lem3359409 _87290 s _35061 f _35062) (@lem3359425 _87290 s _35061 f _35062)). Qed.
Lemma lem3359428 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3359429 (x : Prop) : (x = x) = True.
Proof. exact (@lem3359428 Prop x). Qed.
Lemma lem3359430 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : ((term360 _87290 s _35061 f _35062) = (term360 _87290 s _35061 f _35062)) = True.
Proof. exact (@lem3359429 (term360 _87290 s _35061 f _35062)). Qed.
Lemma lem3359431 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : ((term330 _87290 s f _35062 _35061) = (term360 _87290 s _35061 f _35062)) = True.
Proof. exact (TRANS (@lem3359426 _87290 s _35061 f _35062) (@lem3359430 _87290 s _35061 f _35062)). Qed.
Lemma lem3359432 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : True = ((term330 _87290 s f _35062 _35061) = (term360 _87290 s _35061 f _35062)).
Proof. exact (SYM (@lem3359431 _87290 s _35061 f _35062)). Qed.
Lemma lem3359433 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term330 _87290 s f _35062 _35061) = (term360 _87290 s _35061 f _35062).
Proof. exact (EQ_MP (@lem3359432 _87290 s _35061 f _35062) (@lem0)). Qed.
Lemma lem3359434 {_87290 : Type'} (_35061 : _87290) (_35062 : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term360 _87290 s _35061 f _35062.
Proof. exact (EQ_MP (@lem3359433 _87290 s _35061 f _35062) (@lem3359326 _87290 _35062 _35061 f s t x h1)). Qed.
Lemma lem3359436 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3359437 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (_35062 : _87290 -> Prop) (_35061 : _87290) : (term360 _87290 s _35061 f _35062) = (term364 _87290 s f _35062 _35061).
Proof. exact (@lem3359436 (term365 _87290 s _35061 f _35062) (@I (_87290 -> Prop) _35062 _35061)). Qed.
Lemma lem3359439 (a : Prop) (b : Prop) : (term366 a b) = (term367 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3359440 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term368 _87290 s _35061 f _35062) = (term369 _87290 s _35061 f _35062).
Proof. exact (@lem3359439 (term289 _87290 s _35061) (term295 _87290 f _35062)). Qed.
Lemma lem3359442 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3359443 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) : (term370 _87290 s _35061) = (@I (_87290 -> Prop) s _35061).
Proof. exact (@lem3359442 (@I (_87290 -> Prop) s _35061)). Qed.
Lemma lem3359444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359445 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) : (term371 _87290 s _35061) = (term302 _87290 s _35061).
Proof. exact (MK_COMB (@lem3359444) (@lem3359443 _87290 s _35061)). Qed.
Lemma lem3359447 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3359448 {_87290 : Type'} (f : type686 _87290) (_35062 : _87290 -> Prop) : (term372 _87290 f _35062) = (@I ((_87290 -> Prop) -> Prop) f _35062).
Proof. exact (@lem3359447 (@I ((_87290 -> Prop) -> Prop) f _35062)). Qed.
Lemma lem3359449 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term369 _87290 s _35061 f _35062) = (term373 _87290 s _35061 f _35062).
Proof. exact (MK_COMB (@lem3359445 _87290 s _35061) (@lem3359448 _87290 f _35062)). Qed.
Lemma lem3359450 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term368 _87290 s _35061 f _35062) = (term373 _87290 s _35061 f _35062).
Proof. exact (TRANS (@lem3359440 _87290 s _35061 f _35062) (@lem3359449 _87290 s _35061 f _35062)). Qed.
Lemma lem3359451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359452 {_87290 : Type'} (s : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (_35062 : _87290 -> Prop) : (term374 _87290 s _35061 f _35062) = (term375 _87290 s _35061 f _35062).
Proof. exact (MK_COMB (@lem3359451) (@lem3359450 _87290 s _35061 f _35062)). Qed.
Lemma lem3359453 {_87290 : Type'} (_35062 : _87290 -> Prop) (_35061 : _87290) : (@I (_87290 -> Prop) _35062 _35061) = (@I (_87290 -> Prop) _35062 _35061).
Proof. exact (eq_refl (@I (_87290 -> Prop) _35062 _35061)). Qed.
Lemma lem3359454 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (_35062 : _87290 -> Prop) (_35061 : _87290) : (term364 _87290 s f _35062 _35061) = (term376 _87290 s f _35062 _35061).
Proof. exact (MK_COMB (@lem3359452 _87290 s _35061 f _35062) (@lem3359453 _87290 _35062 _35061)). Qed.
Lemma lem3359455 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (_35062 : _87290 -> Prop) (_35061 : _87290) : (term360 _87290 s _35061 f _35062) = (term376 _87290 s f _35062 _35061).
Proof. exact (TRANS (@lem3359437 _87290 s f _35062 _35061) (@lem3359454 _87290 s f _35062 _35061)). Qed.
Lemma lem3359457 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term373 _87290 s x f t.
Proof. exact (conj (@lem3359355 _87290 f s t x h1) (@lem3359362 _87290 f s t x h1)). Qed.
Lemma lem3359459 {_87290 : Type'} (_35062 : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term376 _87290 s f _35062 _35061.
Proof. exact (EQ_MP (@lem3359455 _87290 s f _35062 _35061) (@lem3359434 _87290 _35061 _35062 f s t x h1)). Qed.
Lemma lem3359460 {_87290 : Type'} (_35062 : _87290 -> Prop) (_35061 : _87290) (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term376 _87290 s f _35062 _35061.
Proof. exact (@lem3359459 _87290 _35062 _35061 f s t x h1). Qed.
Lemma lem3359461 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term376 _87290 s f t x.
Proof. exact (@lem3359460 _87290 t x f s t x h1). Qed.
Lemma lem3359464 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : @I (_87290 -> Prop) t x.
Proof. exact (@lem3359461 _87290 f s t x h1 (@lem3359457 _87290 f s t x h1)). Qed.
Lemma lem3359465 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term354 _87290 t x.
Proof. exact (fun h0 : term289 _87290 t x => @lem3359464 _87290 f s t x h1). Qed.
Lemma lem3359467 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359468 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (term354 _87290 t x) = (@I (_87290 -> Prop) t x).
Proof. exact (@lem3359467 (@I (_87290 -> Prop) t x)). Qed.
Lemma lem3359469 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : @I (_87290 -> Prop) t x.
Proof. exact (EQ_MP (@lem3359468 _87290 t x) (@lem3359465 _87290 f s t x h1)). Qed.
Lemma lem3359472 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3359474 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) : (term289 _87290 t x) = (term377 _87290 t x).
Proof. exact (@lem3359472 (@I (_87290 -> Prop) t x)). Qed.
Lemma lem3359477 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term377 _87290 t x.
Proof. exact (EQ_MP (@lem3359474 _87290 t x) (@lem3359332 _87290 f s t x h1)). Qed.
Lemma lem3359480 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : False.
Proof. exact (@lem3359477 _87290 f s t x h1 (@lem3359469 _87290 f s t x h1)). Qed.
Lemma lem3359481 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : term378.
Proof. exact (fun h0 : ~ False => @lem3359480 _87290 f s t x h1). Qed.
Lemma lem3359483 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359484 : term378 = False.
Proof. exact (@lem3359483 False). Qed.
Lemma lem3359485 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (t : _87290 -> Prop) (x : _87290) (h1 : term315 _87290 f s t x) : False.
Proof. exact (EQ_MP (@lem3359484) (@lem3359481 _87290 f s t x h1)). Qed.
Lemma lem3359487 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : @I ((_87290 -> Prop) -> Prop) f t'.
Proof. exact (proj1 (@lem3359189 _87290 t' x f s h1)). Qed.
Lemma lem3359488 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term356 _87290 f t'.
Proof. exact (fun h0 : term295 _87290 f t' => @lem3359487 _87290 t' x f s h1). Qed.
Lemma lem3359490 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359491 {_87290 : Type'} (f : type686 _87290) (t' : _87290 -> Prop) : (term356 _87290 f t') = (@I ((_87290 -> Prop) -> Prop) f t').
Proof. exact (@lem3359490 (@I ((_87290 -> Prop) -> Prop) f t')). Qed.
Lemma lem3359492 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : @I ((_87290 -> Prop) -> Prop) f t'.
Proof. exact (EQ_MP (@lem3359491 _87290 f t') (@lem3359488 _87290 t' x f s h1)). Qed.
Lemma lem3359494 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : @I (_87290 -> Prop) s x.
Proof. exact (proj1 (@lem3359188 _87290 t' x f s h1)). Qed.
Lemma lem3359495 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term354 _87290 s x.
Proof. exact (fun h0 : term289 _87290 s x => @lem3359494 _87290 t' x f s h1). Qed.
Lemma lem3359497 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359498 {_87290 : Type'} (s : _87290 -> Prop) (x : _87290) : (term354 _87290 s x) = (@I (_87290 -> Prop) s x).
Proof. exact (@lem3359497 (@I (_87290 -> Prop) s x)). Qed.
Lemma lem3359499 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : @I (_87290 -> Prop) s x.
Proof. exact (EQ_MP (@lem3359498 _87290 s x) (@lem3359495 _87290 t' x f s h1)). Qed.
Lemma lem3359505 (q : Prop) (p : Prop) (r : Prop) : (term359 p q r) = (term359 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3359506 {_87290 : Type'} (s : _87290 -> Prop) (f : type686 _87290) (_35063 : _87290 -> Prop) (_35064 : _87290) : (term344 _87290 f s _35063 _35064) = (term330 _87290 s f _35063 _35064).
Proof. exact (@lem3359505 (term289 _87290 s _35064) (term295 _87290 f _35063) (@I (_87290 -> Prop) _35063 _35064)). Qed.
Lemma lem3359520 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3359521 {_87290 : Type'} (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term308 _87290 f _35063 _35064) = (term357 _87290 _35064 f _35063).
Proof. exact (@lem3359520 (@I (_87290 -> Prop) _35063 _35064) (term295 _87290 f _35063)). Qed.
Lemma lem3359527 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) : (term290 _87290 s _35064) = (term290 _87290 s _35064).
Proof. exact (eq_refl (term290 _87290 s _35064)). Qed.
Lemma lem3359528 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term330 _87290 s f _35063 _35064) = (term358 _87290 s _35064 f _35063).
Proof. exact (MK_COMB (@lem3359527 _87290 s _35064) (@lem3359521 _87290 _35064 f _35063)). Qed.
Lemma lem3359532 (q : Prop) (p : Prop) (r : Prop) : (term359 p q r) = (term359 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3359533 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term358 _87290 s _35064 f _35063) = (term360 _87290 s _35064 f _35063).
Proof. exact (@lem3359532 (@I (_87290 -> Prop) _35063 _35064) (term289 _87290 s _35064) (term295 _87290 f _35063)). Qed.
Lemma lem3359549 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term330 _87290 s f _35063 _35064) = (term360 _87290 s _35064 f _35063).
Proof. exact (TRANS (@lem3359528 _87290 s _35064 f _35063) (@lem3359533 _87290 s _35064 f _35063)). Qed.
Lemma lem3359550 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term344 _87290 f s _35063 _35064) = (term360 _87290 s _35064 f _35063).
Proof. exact (TRANS (@lem3359506 _87290 s f _35063 _35064) (@lem3359549 _87290 s _35064 f _35063)). Qed.
Lemma lem3359551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3359552 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term379 _87290 f s _35063 _35064) = (term362 _87290 s _35064 f _35063).
Proof. exact (MK_COMB (@lem3359551) (@lem3359550 _87290 s _35064 f _35063)). Qed.
Lemma lem3359566 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3359567 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term380 _87290 f _35063 s _35064) = (term365 _87290 s _35064 f _35063).
Proof. exact (@lem3359566 (term289 _87290 s _35064) (term295 _87290 f _35063)). Qed.
Lemma lem3359573 {_87290 : Type'} (_35063 : _87290 -> Prop) (_35064 : _87290) : (term381 _87290 _35063 _35064) = (term381 _87290 _35063 _35064).
Proof. exact (eq_refl (term381 _87290 _35063 _35064)). Qed.
Lemma lem3359574 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : (term382 _87290 f _35063 s _35064) = (term360 _87290 s _35064 f _35063).
Proof. exact (MK_COMB (@lem3359573 _87290 _35063 _35064) (@lem3359567 _87290 s _35064 f _35063)). Qed.
Lemma lem3359585 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : ((term344 _87290 f s _35063 _35064) = (term382 _87290 f _35063 s _35064)) = ((term360 _87290 s _35064 f _35063) = (term360 _87290 s _35064 f _35063)).
Proof. exact (MK_COMB (@lem3359552 _87290 s _35064 f _35063) (@lem3359574 _87290 s _35064 f _35063)). Qed.
Lemma lem3359587 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3359588 (x : Prop) : (x = x) = True.
Proof. exact (@lem3359587 Prop x). Qed.
Lemma lem3359589 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) (f : type686 _87290) (_35063 : _87290 -> Prop) : ((term360 _87290 s _35064 f _35063) = (term360 _87290 s _35064 f _35063)) = True.
Proof. exact (@lem3359588 (term360 _87290 s _35064 f _35063)). Qed.
Lemma lem3359590 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) (s : _87290 -> Prop) (_35064 : _87290) : ((term344 _87290 f s _35063 _35064) = (term382 _87290 f _35063 s _35064)) = True.
Proof. exact (TRANS (@lem3359585 _87290 s _35064 f _35063) (@lem3359589 _87290 s _35064 f _35063)). Qed.
Lemma lem3359591 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) (s : _87290 -> Prop) (_35064 : _87290) : True = ((term344 _87290 f s _35063 _35064) = (term382 _87290 f _35063 s _35064)).
Proof. exact (SYM (@lem3359590 _87290 f _35063 s _35064)). Qed.
Lemma lem3359592 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) (s : _87290 -> Prop) (_35064 : _87290) : (term344 _87290 f s _35063 _35064) = (term382 _87290 f _35063 s _35064).
Proof. exact (EQ_MP (@lem3359591 _87290 f _35063 s _35064) (@lem0)). Qed.
Lemma lem3359593 {_87290 : Type'} (_35063 : _87290 -> Prop) (_35064 : _87290) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term382 _87290 f _35063 s _35064.
Proof. exact (EQ_MP (@lem3359592 _87290 f _35063 s _35064) (@lem3359342 _87290 _35063 _35064 t' x f s h1)). Qed.
Lemma lem3359595 (b : Prop) (a : Prop) : (a \/ b) = (term363 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3359596 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (_35063 : _87290 -> Prop) (_35064 : _87290) : (term382 _87290 f _35063 s _35064) = (term383 _87290 f s _35063 _35064).
Proof. exact (@lem3359595 (term380 _87290 f _35063 s _35064) (@I (_87290 -> Prop) _35063 _35064)). Qed.
Lemma lem3359598 (a : Prop) (b : Prop) : (term366 a b) = (term367 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3359599 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) (s : _87290 -> Prop) (_35064 : _87290) : (term384 _87290 f _35063 s _35064) = (term385 _87290 f _35063 s _35064).
Proof. exact (@lem3359598 (term295 _87290 f _35063) (term289 _87290 s _35064)). Qed.
Lemma lem3359601 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3359602 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) : (term372 _87290 f _35063) = (@I ((_87290 -> Prop) -> Prop) f _35063).
Proof. exact (@lem3359601 (@I ((_87290 -> Prop) -> Prop) f _35063)). Qed.
Lemma lem3359603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3359604 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) : (term386 _87290 f _35063) = (term300 _87290 f _35063).
Proof. exact (MK_COMB (@lem3359603) (@lem3359602 _87290 f _35063)). Qed.
Lemma lem3359606 (a : Prop) : (term55 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3359607 {_87290 : Type'} (s : _87290 -> Prop) (_35064 : _87290) : (term370 _87290 s _35064) = (@I (_87290 -> Prop) s _35064).
Proof. exact (@lem3359606 (@I (_87290 -> Prop) s _35064)). Qed.
Lemma lem3359608 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) (s : _87290 -> Prop) (_35064 : _87290) : (term385 _87290 f _35063 s _35064) = (term387 _87290 f _35063 s _35064).
Proof. exact (MK_COMB (@lem3359604 _87290 f _35063) (@lem3359607 _87290 s _35064)). Qed.
Lemma lem3359609 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) (s : _87290 -> Prop) (_35064 : _87290) : (term384 _87290 f _35063 s _35064) = (term387 _87290 f _35063 s _35064).
Proof. exact (TRANS (@lem3359599 _87290 f _35063 s _35064) (@lem3359608 _87290 f _35063 s _35064)). Qed.
Lemma lem3359610 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3359611 {_87290 : Type'} (f : type686 _87290) (_35063 : _87290 -> Prop) (s : _87290 -> Prop) (_35064 : _87290) : (term388 _87290 f _35063 s _35064) = (term389 _87290 f _35063 s _35064).
Proof. exact (MK_COMB (@lem3359610) (@lem3359609 _87290 f _35063 s _35064)). Qed.
Lemma lem3359612 {_87290 : Type'} (_35063 : _87290 -> Prop) (_35064 : _87290) : (@I (_87290 -> Prop) _35063 _35064) = (@I (_87290 -> Prop) _35063 _35064).
Proof. exact (eq_refl (@I (_87290 -> Prop) _35063 _35064)). Qed.
Lemma lem3359613 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (_35063 : _87290 -> Prop) (_35064 : _87290) : (term383 _87290 f s _35063 _35064) = (term390 _87290 f s _35063 _35064).
Proof. exact (MK_COMB (@lem3359611 _87290 f _35063 s _35064) (@lem3359612 _87290 _35063 _35064)). Qed.
Lemma lem3359614 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (_35063 : _87290 -> Prop) (_35064 : _87290) : (term382 _87290 f _35063 s _35064) = (term390 _87290 f s _35063 _35064).
Proof. exact (TRANS (@lem3359596 _87290 f s _35063 _35064) (@lem3359613 _87290 f s _35063 _35064)). Qed.
Lemma lem3359616 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term387 _87290 f t' s x.
Proof. exact (conj (@lem3359492 _87290 t' x f s h1) (@lem3359499 _87290 t' x f s h1)). Qed.
Lemma lem3359618 {_87290 : Type'} (_35063 : _87290 -> Prop) (_35064 : _87290) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term390 _87290 f s _35063 _35064.
Proof. exact (EQ_MP (@lem3359614 _87290 f s _35063 _35064) (@lem3359593 _87290 _35063 _35064 t' x f s h1)). Qed.
Lemma lem3359619 {_87290 : Type'} (_35063 : _87290 -> Prop) (_35064 : _87290) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term390 _87290 f s _35063 _35064.
Proof. exact (@lem3359618 _87290 _35063 _35064 t' x f s h1). Qed.
Lemma lem3359620 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term390 _87290 f s t' x.
Proof. exact (@lem3359619 _87290 t' x t' x f s h1). Qed.
Lemma lem3359623 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : @I (_87290 -> Prop) t' x.
Proof. exact (@lem3359620 _87290 t' x f s h1 (@lem3359616 _87290 t' x f s h1)). Qed.
Lemma lem3359624 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term354 _87290 t' x.
Proof. exact (fun h0 : term289 _87290 t' x => @lem3359623 _87290 t' x f s h1). Qed.
Lemma lem3359626 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359627 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) : (term354 _87290 t' x) = (@I (_87290 -> Prop) t' x).
Proof. exact (@lem3359626 (@I (_87290 -> Prop) t' x)). Qed.
Lemma lem3359628 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : @I (_87290 -> Prop) t' x.
Proof. exact (EQ_MP (@lem3359627 _87290 t' x) (@lem3359624 _87290 t' x f s h1)). Qed.
Lemma lem3359631 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3359633 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) : (term289 _87290 t' x) = (term377 _87290 t' x).
Proof. exact (@lem3359631 (@I (_87290 -> Prop) t' x)). Qed.
Lemma lem3359636 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term377 _87290 t' x.
Proof. exact (EQ_MP (@lem3359633 _87290 t' x) (@lem3359348 _87290 t' x f s h1)). Qed.
Lemma lem3359639 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : False.
Proof. exact (@lem3359636 _87290 t' x f s h1 (@lem3359628 _87290 t' x f s h1)). Qed.
Lemma lem3359640 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : term378.
Proof. exact (fun h0 : ~ False => @lem3359639 _87290 t' x f s h1). Qed.
Lemma lem3359642 (p : Prop) : (term355 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3359643 : term378 = False.
Proof. exact (@lem3359642 False). Qed.
Lemma lem3359644 {_87290 : Type'} (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term305 _87290 t' x f s) : False.
Proof. exact (EQ_MP (@lem3359643) (@lem3359640 _87290 t' x f s h1)). Qed.
Lemma lem3359645 {_87290 : Type'} (t : _87290 -> Prop) (t' : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term280 _87290 t t' x f s) : False.
Proof. exact (or_elim (@lem3359178 _87290 t t' x f s h1) (fun h0 : term315 _87290 f s t x => @lem3359485 _87290 f s t x h0) (fun h0 : term305 _87290 t' x f s => @lem3359644 _87290 t' x f s h0)). Qed.
Lemma lem3359646 {_87290 : Type'} (t : _87290 -> Prop) (x : _87290) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term283 _87290 t x f s) : False.
Proof. exact (ex_elim (@lem3359023 _87290 t x f s h1) (fun t' : _87290 -> Prop => fun h0 : term282 _87290 t x f s t' => @lem3359645 _87290 t t' x f s h0)). Qed.
Lemma lem3359647 {_87290 : Type'} (t : _87290 -> Prop) (f : type686 _87290) (s : _87290 -> Prop) (h1 : term285 _87290 t f s) : False.
Proof. exact (ex_elim (@lem3359022 _87290 t f s h1) (fun x : _87290 => fun h0 : term284 _87290 t f s x => @lem3359646 _87290 t x f s h0)). Qed.
Lemma lem3359648 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (h1 : term57 _87290 f s) : False.
Proof. exact (ex_elim (@lem3359021 _87290 f s h1) (fun t : _87290 -> Prop => fun h0 : term286 _87290 f s t => @lem3359647 _87290 t f s h0)). Qed.
Lemma lem3359649 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (h1 : term57 _87290 f s) : (term57 _87290 f s) = False.
Proof. exact (prop_ext (fun h2 : term57 _87290 f s => @lem3359648 _87290 f s h1) (fun h2 : False => @lem3358379 _87290 f s h1)). Qed.
Lemma lem3359650 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) (h1 : term57 _87290 f s) : False.
Proof. exact (EQ_MP (@lem3359649 _87290 f s h1) (@lem3358379 _87290 f s h1)). Qed.
Lemma lem3359651 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : term56 _87290 f s.
Proof. exact (fun h0 : term57 _87290 f s => @lem3359650 _87290 f s h0). Qed.
Lemma lem3359652 {_87290 : Type'} (f : type686 _87290) (s : _87290 -> Prop) : (term34 _87290 s f) = (term43 _87290 f s).
Proof. exact (EQ_MP (@lem3358378 _87290 f s) (@lem3359651 _87290 f s)). Qed.
Lemma lem3359657 {_87290 : Type'} (s : _87290 -> Prop) : term45 _87290 s.
Proof. exact (fun f : type686 _87290 => @lem3359652 _87290 f s). Qed.
Lemma lem3359662 {_87290 : Type'} : term47 _87290.
Proof. exact (fun s : _87290 -> Prop => @lem3359657 _87290 s). Qed.
Lemma lem3359663 {_87290 : Type'} : term49 _87290.
Proof. exact (EQ_MP (@lem3358374 _87290) (@lem3359662 _87290)). Qed.
Lemma lem3359665 {_87290 : Type'} : term49 _87290.
Proof. exact (@lem3358244 _87290 (@lem3359663 _87290)). Qed.
Lemma lem3359666 {_87290 : Type'} (h1 : term50 _87290) : False.
Proof. exact (@lem3359665 _87290 (@lem3358228 _87290 h1)). Qed.
Lemma lem3359667 {_87290 : Type'} (h1 : term50 _87290) : (term50 _87290) = False.
Proof. exact (prop_ext (fun h2 : term50 _87290 => @lem3359666 _87290 h1) (fun h2 : False => @lem3358228 _87290 h1)). Qed.
Lemma lem3359668 {_87290 : Type'} (h1 : term50 _87290) : False.
Proof. exact (EQ_MP (@lem3359667 _87290 h1) (@lem3358228 _87290 h1)). Qed.
Lemma lem3359669 {_87290 : Type'} : term49 _87290.
Proof. exact (fun h0 : term50 _87290 => @lem3359668 _87290 h0). Qed.
Lemma lem3359670 {_87290 : Type'} : term47 _87290.
Proof. exact (EQ_MP (@lem3358227 _87290) (@lem3359669 _87290)). Qed.
Lemma lem3359671 {_87290 : Type'} : term19 _87290.
Proof. exact (EQ_MP (@lem3358223 _87290) (@lem3359670 _87290)). Qed.
Lemma lem3359672 {_87290 : Type'} : term18 _87290.
Proof. exact (EQ_MP (@lem3358092 _87290) (@lem3359671 _87290)). Qed.
