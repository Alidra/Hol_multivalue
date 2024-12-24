Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_BOUND_LT_term_abbrevs.
Require Import REAL_LTE_TRANS_spec.
Require Import SUM_CONST_spec.
Require Import SUM_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm7_spec.
Lemma lem7137144 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7137145 {A : Type'} (f : A -> real) (h1 : term0 A) : term1 A f.
Proof. exact (@lem7137144 A h1 f). Qed.
Lemma lem7137146 {A : Type'} (f : A -> real) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem7137147 {A : Type'} (f : A -> real) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem7137146 A f) (@lem7137145 A f h1)). Qed.
Lemma lem7137148 {A : Type'} (f : A -> real) (g : A -> real) (h1 : term0 A) : term3 A f g.
Proof. exact (@lem7137147 A f h1 g). Qed.
Lemma lem7137149 {A : Type'} (f : A -> real) (g : A -> real) : (term3 A f g) = (term4 A f g).
Proof. exact (eq_refl (term3 A f g)). Qed.
Lemma lem7137150 {A : Type'} (f : A -> real) (g : A -> real) (h1 : term0 A) : term4 A f g.
Proof. exact (EQ_MP (@lem7137149 A f g) (@lem7137148 A f g h1)). Qed.
Lemma lem7137151 {A : Type'} (f : A -> real) (g : A -> real) (s : A -> Prop) (h1 : term0 A) : term5 A f g s.
Proof. exact (@lem7137150 A f g h1 s). Qed.
Lemma lem7137152 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term5 A f g s) = (term6 A f s g).
Proof. exact (eq_refl (term5 A f g s)). Qed.
Lemma lem7137153 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term0 A) : term6 A f s g.
Proof. exact (EQ_MP (@lem7137152 A f s g) (@lem7137151 A f g s h1)). Qed.
Lemma lem7137154 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term7 A s f g) : term7 A s f g.
Proof. exact (h1). Qed.
Lemma lem7137155 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A) (h2 : term7 A s f g) : term8 A f s g.
Proof. exact (@lem7137153 A f s g h1 (@lem7137154 A s f g h2)). Qed.
Lemma lem7137156 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term7 A s f g) : term9 A f s g.
Proof. exact (fun h0 : term0 A => @lem7137155 A s f g h0 h1). Qed.
Lemma lem7137157 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7137158 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term0 A) (h2 : term7 A s f g) : term8 A f s g.
Proof. exact (@lem7137156 A s f g h2 (@lem7137157 A h1)). Qed.
Lemma lem7137159 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (h1 : term0 A) : term6 A f s g.
Proof. exact (fun h0 : term7 A s f g => @lem7137158 A s f g h1 h0). Qed.
Lemma lem7137160 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term0 A) : term10 A f s.
Proof. exact (fun g : A -> real => @lem7137159 A f s g h1). Qed.
Lemma lem7137161 {A : Type'} (f : A -> real) (h1 : term0 A) : term11 A f.
Proof. exact (fun s : A -> Prop => @lem7137160 A f s h1). Qed.
Lemma lem7137162 {A : Type'} (h1 : term0 A) : term12 A.
Proof. exact (fun f : A -> real => @lem7137161 A f h1). Qed.
Lemma lem7137163 {A : Type'} : term13 A.
Proof. exact (fun h0 : term0 A => @lem7137162 A h0). Qed.
Lemma lem7137164 {A : Type'} : term12 A.
Proof. exact (@lem7137163 A (@lem7073063 A)). Qed.
Lemma lem7137165 {A : Type'} (f : A -> real) : term14 A f.
Proof. exact (@lem7137164 A f). Qed.
Lemma lem7137166 {A : Type'} (f : A -> real) : (term14 A f) = (term11 A f).
Proof. exact (eq_refl (term14 A f)). Qed.
Lemma lem7137167 {A : Type'} (f : A -> real) : term11 A f.
Proof. exact (EQ_MP (@lem7137166 A f) (@lem7137165 A f)). Qed.
Lemma lem7137168 {A : Type'} (f : A -> real) (s : A -> Prop) : term15 A f s.
Proof. exact (@lem7137167 A f s). Qed.
Lemma lem7137169 {A : Type'} (f : A -> real) (s : A -> Prop) : (term15 A f s) = (term10 A f s).
Proof. exact (eq_refl (term15 A f s)). Qed.
Lemma lem7137170 {A : Type'} (f : A -> real) (s : A -> Prop) : term10 A f s.
Proof. exact (EQ_MP (@lem7137169 A f s) (@lem7137168 A f s)). Qed.
Lemma lem7137171 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term16 A f s g.
Proof. exact (@lem7137170 A f s g). Qed.
Lemma lem7137172 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term16 A f s g) = (term6 A f s g).
Proof. exact (eq_refl (term16 A f s g)). Qed.
Lemma lem7137174 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem7137175 (x : real) (h1 : term17) : term18 x.
Proof. exact (@lem7137174 h1 x). Qed.
Lemma lem7137176 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem7137177 (x : real) (h1 : term17) : term19 x.
Proof. exact (EQ_MP (@lem7137176 x) (@lem7137175 x h1)). Qed.
Lemma lem7137178 (x : real) (y : real) (h1 : term17) : term20 x y.
Proof. exact (@lem7137177 x h1 y). Qed.
Lemma lem7137179 (y : real) (x : real) : (term20 x y) = (term21 y x).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem7137180 (y : real) (x : real) (h1 : term17) : term21 y x.
Proof. exact (EQ_MP (@lem7137179 y x) (@lem7137178 x y h1)). Qed.
Lemma lem7137181 (y : real) (x : real) (z : real) (h1 : term17) : term22 y x z.
Proof. exact (@lem7137180 y x h1 z). Qed.
Lemma lem7137182 (y : real) (x : real) (z : real) : (term22 y x z) = (term23 y x z).
Proof. exact (eq_refl (term22 y x z)). Qed.
Lemma lem7137183 (y : real) (x : real) (z : real) (h1 : term17) : term23 y x z.
Proof. exact (EQ_MP (@lem7137182 y x z) (@lem7137181 y x z h1)). Qed.
Lemma lem7137184 (x : real) (y : real) (z : real) (h1 : term24 x y z) : term24 x y z.
Proof. exact (h1). Qed.
Lemma lem7137185 (x : real) (y : real) (z : real) (h1 : term17) (h2 : term24 x y z) : real_lt x z.
Proof. exact (@lem7137183 y x z h1 (@lem7137184 x y z h2)). Qed.
Lemma lem7137186 (x : real) (y : real) (z : real) (h1 : term24 x y z) : term25 x z.
Proof. exact (fun h0 : term17 => @lem7137185 x y z h0 h1). Qed.
Lemma lem7137187 (x : real) (z : real) (h1 : term26 x z) : term26 x z.
Proof. exact (h1). Qed.
Lemma lem7137188 (x : real) (z : real) (h1 : term26 x z) : term25 x z.
Proof. exact (ex_elim (@lem7137187 x z h1) (fun y : real => fun h0 : term27 x z y => @lem7137186 x y z h0)). Qed.
Lemma lem7137189 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem7137190 (x : real) (z : real) (h1 : term17) (h2 : term26 x z) : real_lt x z.
Proof. exact (@lem7137188 x z h2 (@lem7137189 h1)). Qed.
Lemma lem7137191 (x : real) (z : real) (h1 : term17) : term28 x z.
Proof. exact (fun h0 : term26 x z => @lem7137190 x z h1 h0). Qed.
Lemma lem7137192 (x : real) (h1 : term17) : term29 x.
Proof. exact (fun z : real => @lem7137191 x z h1). Qed.
Lemma lem7137193 (h1 : term17) : term30.
Proof. exact (fun x : real => @lem7137192 x h1). Qed.
Lemma lem7137194 : term31.
Proof. exact (fun h0 : term17 => @lem7137193 h0). Qed.
Lemma lem7137195 : term30.
Proof. exact (@lem7137194 (@lem1370312)). Qed.
Lemma lem7137196 (x : real) : term32 x.
Proof. exact (@lem7137195 x). Qed.
Lemma lem7137197 (x : real) : (term32 x) = (term29 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem7137198 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem7137197 x) (@lem7137196 x)). Qed.
Lemma lem7137199 (x : real) (z : real) : term33 x z.
Proof. exact (@lem7137198 x z). Qed.
Lemma lem7137200 (x : real) (z : real) : (term33 x z) = (term28 x z).
Proof. exact (eq_refl (term33 x z)). Qed.
Lemma lem7137202 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term34 A s f b) : term34 A s f b.
Proof. exact (h1). Qed.
Lemma lem7137203 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term35 A s f b) : term35 A s f b.
Proof. exact (h1). Qed.
Lemma lem7137204 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7137205 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term36 A s f b) : term36 A s f b.
Proof. exact (h1). Qed.
Lemma lem7137206 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : term37 A s f b.
Proof. exact (h1). Qed.
Lemma lem7137207 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term38 A s f x b) : term38 A s f x b.
Proof. exact (h1). Qed.
Lemma lem7137208 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem7137209 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7137211 (x : real) (z : real) : term28 x z.
Proof. exact (EQ_MP (@lem7137200 x z) (@lem7137199 x z)). Qed.
Lemma lem7137212 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term40 A f s b.
Proof. exact (@lem7137211 (@sum A s f) (term41 A s b)). Qed.
Lemma lem7137214 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term6 A f s g.
Proof. exact (EQ_MP (@lem7137172 A f s g) (@lem7137171 A f s g)). Qed.
Lemma lem7137215 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : term6 A f s g.
Proof. exact (@lem7137214 A f s g). Qed.
Lemma lem7137216 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term42 A f s b.
Proof. exact (@lem7137215 A f s (term43 A b)). Qed.
Lemma lem7137217 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7137219 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : term44 A s f b x.
Proof. exact (@lem7137206 A s f b h1 x). Qed.
Lemma lem7137220 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term44 A s f b x) = (term45 A s f x b).
Proof. exact (eq_refl (term44 A s f b x)). Qed.
Lemma lem7137221 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : term45 A s f x b.
Proof. exact (EQ_MP (@lem7137220 A s f x b) (@lem7137219 A x s f b h1)). Qed.
Lemma lem7137222 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term45 A s f x b) = ((term45 A s f x b) = True).
Proof. exact (@lem7 (term45 A s f x b)). Qed.
Lemma lem7137231 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7137217 A s) (@lem7137204 A s h1)). Qed.
Lemma lem7137232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7137233 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term46 A s) = (and True).
Proof. exact (MK_COMB (@lem7137232) (@lem7137231 A s h1)). Qed.
Lemma lem7137269 {A B : Type'} (f : A -> B) (y : A) : (term47 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7137270 {A : Type'} (f : A -> real) (y : A) : (term48 A f y) = (f y).
Proof. exact (@lem7137269 A real f y). Qed.
Lemma lem7137271 {A : Type'} (b : real) (_95330 : A) : (term49 A b _95330) = (term50 A b _95330).
Proof. exact (@lem7137270 A (term43 A b) _95330). Qed.
Lemma lem7137272 {A : Type'} (x : A) (b : real) : (term50 A b x) = b.
Proof. exact (eq_refl (term50 A b x)). Qed.
Lemma lem7137273 {A : Type'} (b : real) : (term51 A b) = (term43 A b).
Proof. exact (fun_ext (fun x : A => @lem7137272 A x b)). Qed.
Lemma lem7137274 {A : Type'} (_95330 : A) : _95330 = _95330.
Proof. exact (eq_refl _95330). Qed.
Lemma lem7137275 {A : Type'} (b : real) (_95330 : A) : (term49 A b _95330) = (term50 A b _95330).
Proof. exact (MK_COMB (@lem7137273 A b) (@lem7137274 A _95330)). Qed.
Lemma lem7137276 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7137277 {A : Type'} (b : real) (_95330 : A) : (term52 A b _95330) = (term53 A b _95330).
Proof. exact (MK_COMB (@lem7137276) (@lem7137275 A b _95330)). Qed.
Lemma lem7137278 {A : Type'} (_95330 : A) (b : real) : (term50 A b _95330) = b.
Proof. exact (eq_refl (term50 A b _95330)). Qed.
Lemma lem7137279 {A : Type'} (_95330 : A) (b : real) : ((term49 A b _95330) = (term50 A b _95330)) = ((term50 A b _95330) = b).
Proof. exact (MK_COMB (@lem7137277 A b _95330) (@lem7137278 A _95330 b)). Qed.
Lemma lem7137280 {A : Type'} (_95330 : A) (b : real) : (term50 A b _95330) = b.
Proof. exact (EQ_MP (@lem7137279 A _95330 b) (@lem7137271 A b _95330)). Qed.
Lemma lem7137281 {A : Type'} (f : A -> real) (_95330 : A) : (term54 A f _95330) = (term54 A f _95330).
Proof. exact (eq_refl (term54 A f _95330)). Qed.
Lemma lem7137282 {A : Type'} (f : A -> real) (_95330 : A) (b : real) : (term55 A f b _95330) = (term56 A f _95330 b).
Proof. exact (MK_COMB (@lem7137281 A f _95330) (@lem7137280 A _95330 b)). Qed.
Lemma lem7137283 {A : Type'} (_95330 : A) (s : A -> Prop) : (term57 A _95330 s) = (term57 A _95330 s).
Proof. exact (eq_refl (term57 A _95330 s)). Qed.
Lemma lem7137284 {A : Type'} (s : A -> Prop) (f : A -> real) (_95330 : A) (b : real) : (term58 A s f b _95330) = (term45 A s f _95330 b).
Proof. exact (MK_COMB (@lem7137283 A _95330 s) (@lem7137282 A f _95330 b)). Qed.
Lemma lem7137286 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term45 A s f x b) = True.
Proof. exact (EQ_MP (@lem7137222 A s f x b) (@lem7137221 A x s f b h1)). Qed.
Lemma lem7137287 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term45 A s f x b) = True.
Proof. exact (@lem7137286 A x s f b h1). Qed.
Lemma lem7137288 {A : Type'} (_95330 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term45 A s f _95330 b) = True.
Proof. exact (@lem7137287 A _95330 s f b h1). Qed.
Lemma lem7137289 {A : Type'} (_95330 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term58 A s f b _95330) = True.
Proof. exact (TRANS (@lem7137284 A s f _95330 b) (@lem7137288 A _95330 s f b h1)). Qed.
Lemma lem7137292 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term59 A s f b) = (term60 A).
Proof. exact (fun_ext (fun _95330 : A => @lem7137289 A _95330 s f b h1)). Qed.
Lemma lem7137293 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137294 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term61 A s f b) = (term62 A).
Proof. exact (MK_COMB (@lem7137293 A) (@lem7137292 A s f b h1)). Qed.
Lemma lem7137296 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7137297 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (@lem7137296 A t). Qed.
Lemma lem7137298 {A : Type'} : (term62 A) = True.
Proof. exact (@lem7137297 A True). Qed.
Lemma lem7137299 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term61 A s f b) = True.
Proof. exact (TRANS (@lem7137294 A s f b h1) (@lem7137298 A)). Qed.
Lemma lem7137300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7137301 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term64 A s f b) = (and True).
Proof. exact (MK_COMB (@lem7137300) (@lem7137299 A s f b h1)). Qed.
Lemma lem7137338 {A B : Type'} (f : A -> B) (y : A) : (term47 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7137339 {A : Type'} (f : A -> real) (y : A) : (term48 A f y) = (f y).
Proof. exact (@lem7137338 A real f y). Qed.
Lemma lem7137340 {A : Type'} (b : real) (_95331 : A) : (term49 A b _95331) = (term50 A b _95331).
Proof. exact (@lem7137339 A (term43 A b) _95331). Qed.
Lemma lem7137341 {A : Type'} (x : A) (b : real) : (term50 A b x) = b.
Proof. exact (eq_refl (term50 A b x)). Qed.
Lemma lem7137342 {A : Type'} (b : real) : (term51 A b) = (term43 A b).
Proof. exact (fun_ext (fun x : A => @lem7137341 A x b)). Qed.
Lemma lem7137343 {A : Type'} (_95331 : A) : _95331 = _95331.
Proof. exact (eq_refl _95331). Qed.
Lemma lem7137344 {A : Type'} (b : real) (_95331 : A) : (term49 A b _95331) = (term50 A b _95331).
Proof. exact (MK_COMB (@lem7137342 A b) (@lem7137343 A _95331)). Qed.
Lemma lem7137345 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7137346 {A : Type'} (b : real) (_95331 : A) : (term52 A b _95331) = (term53 A b _95331).
Proof. exact (MK_COMB (@lem7137345) (@lem7137344 A b _95331)). Qed.
Lemma lem7137347 {A : Type'} (_95331 : A) (b : real) : (term50 A b _95331) = b.
Proof. exact (eq_refl (term50 A b _95331)). Qed.
Lemma lem7137348 {A : Type'} (_95331 : A) (b : real) : ((term49 A b _95331) = (term50 A b _95331)) = ((term50 A b _95331) = b).
Proof. exact (MK_COMB (@lem7137346 A b _95331) (@lem7137347 A _95331 b)). Qed.
Lemma lem7137349 {A : Type'} (_95331 : A) (b : real) : (term50 A b _95331) = b.
Proof. exact (EQ_MP (@lem7137348 A _95331 b) (@lem7137340 A b _95331)). Qed.
Lemma lem7137350 {A : Type'} (f : A -> real) (_95331 : A) : (term65 A f _95331) = (term65 A f _95331).
Proof. exact (eq_refl (term65 A f _95331)). Qed.
Lemma lem7137351 {A : Type'} (f : A -> real) (_95331 : A) (b : real) : (term66 A f b _95331) = (term39 A f _95331 b).
Proof. exact (MK_COMB (@lem7137350 A f _95331) (@lem7137349 A _95331 b)). Qed.
Lemma lem7137352 {A : Type'} (_95331 : A) (s : A -> Prop) : (term67 A _95331 s) = (term67 A _95331 s).
Proof. exact (eq_refl (term67 A _95331 s)). Qed.
Lemma lem7137353 {A : Type'} (s : A -> Prop) (f : A -> real) (_95331 : A) (b : real) : (term68 A s f b _95331) = (term38 A s f _95331 b).
Proof. exact (MK_COMB (@lem7137352 A _95331 s) (@lem7137351 A f _95331 b)). Qed.
Lemma lem7137358 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term69 A s f b) = (term70 A s f b).
Proof. exact (fun_ext (fun _95331 : A => @lem7137353 A s f _95331 b)). Qed.
Lemma lem7137359 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7137360 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term71 A s f b) = (term36 A s f b).
Proof. exact (MK_COMB (@lem7137359 A) (@lem7137358 A s f b)). Qed.
Lemma lem7137365 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term72 A s f b) = (term73 A s f b).
Proof. exact (MK_COMB (@lem7137301 A s f b h1) (@lem7137360 A s f b)). Qed.
Lemma lem7137367 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7137368 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term73 A s f b) = (term36 A s f b).
Proof. exact (@lem7137367 (term36 A s f b)). Qed.
Lemma lem7137388 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) : (term72 A s f b) = (term36 A s f b).
Proof. exact (TRANS (@lem7137365 A s f b h1) (@lem7137368 A s f b)). Qed.
Lemma lem7137389 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : (term74 A s f b) = (term73 A s f b).
Proof. exact (MK_COMB (@lem7137233 A s h2) (@lem7137388 A s f b h1)). Qed.
Lemma lem7137391 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7137392 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term73 A s f b) = (term36 A s f b).
Proof. exact (@lem7137391 (term36 A s f b)). Qed.
Lemma lem7137412 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : (term74 A s f b) = (term36 A s f b).
Proof. exact (TRANS (@lem7137389 A f b s h1 h2) (@lem7137392 A s f b)). Qed.
Lemma lem7137413 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : (term36 A s f b) = (term74 A s f b).
Proof. exact (SYM (@lem7137412 A f b s h1 h2)). Qed.
Lemma lem7137415 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7137416 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term36 A s f b) = (term76 A s f b).
Proof. exact (@lem7137415 (term36 A s f b)). Qed.
Lemma lem7137417 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term76 A s f b) = (term36 A s f b).
Proof. exact (SYM (@lem7137416 A s f b)). Qed.
Lemma lem7137418 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term77 A s f b.
Proof. exact (h1). Qed.
Lemma lem7137421 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term78 A x s f b) : term78 A x s f b.
Proof. exact (h1). Qed.
Lemma lem7137422 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term79 A x s f b.
Proof. exact (fun h0 : term78 A x s f b => @lem7137421 A x s f b h0). Qed.
Lemma lem7137423 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term79 A x s f b) : term79 A x s f b.
Proof. exact (h1). Qed.
Lemma lem7137424 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term78 A x s f b) : term78 A x s f b.
Proof. exact (h1). Qed.
Lemma lem7137425 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term78 A x s f b) (h2 : term79 A x s f b) : term78 A x s f b.
Proof. exact (@lem7137423 A x s f b h2 (@lem7137424 A x s f b h1)). Qed.
Lemma lem7137426 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term78 A x s f b) : term80 A x s f b.
Proof. exact (fun h0 : term79 A x s f b => @lem7137425 A x s f b h1 h0). Qed.
Lemma lem7137427 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term79 A x s f b) : term79 A x s f b.
Proof. exact (h1). Qed.
Lemma lem7137428 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term78 A x s f b) (h2 : term79 A x s f b) : term78 A x s f b.
Proof. exact (@lem7137426 A x s f b h1 (@lem7137427 A x s f b h2)). Qed.
Lemma lem7137429 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term79 A x s f b) : term79 A x s f b.
Proof. exact (fun h0 : term78 A x s f b => @lem7137428 A x s f b h0 h1). Qed.
Lemma lem7137430 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term81 A x s f b.
Proof. exact (fun h0 : term79 A x s f b => @lem7137429 A x s f b h0). Qed.
Lemma lem7137433 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term79 A x s f b.
Proof. exact (@lem7137430 A x s f b (@lem7137422 A x s f b)). Qed.
Lemma lem7137434 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term79 A x s f b.
Proof. exact (@lem7137433 A x s f b). Qed.
Lemma lem7137466 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7137467 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term76 A s f b) = (term82 A s f b).
Proof. exact (@lem7137466 (term77 A s f b)). Qed.
Lemma lem7137469 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7137470 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term82 A s f b) = (term36 A s f b).
Proof. exact (@lem7137469 (term36 A s f b)). Qed.
Lemma lem7137519 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term76 A s f b) = (term36 A s f b).
Proof. exact (TRANS (@lem7137467 A s f b) (@lem7137470 A s f b)). Qed.
Lemma lem7137522 {A : Type'} (f : A -> real) (x : A) (b : real) : (term84 A f x b) = (term84 A f x b).
Proof. exact (eq_refl (term84 A f x b)). Qed.
Lemma lem7137523 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term85 A x s f b) = (term86 A x s f b).
Proof. exact (MK_COMB (@lem7137522 A f x b) (@lem7137519 A s f b)). Qed.
Lemma lem7137526 {A : Type'} (x : A) (s : A -> Prop) : (term57 A x s) = (term57 A x s).
Proof. exact (eq_refl (term57 A x s)). Qed.
Lemma lem7137527 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term87 A x s f b) = (term88 A x s f b).
Proof. exact (MK_COMB (@lem7137526 A x s) (@lem7137523 A x s f b)). Qed.
Lemma lem7137530 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term89 A s f b) = (term89 A s f b).
Proof. exact (eq_refl (term89 A s f b)). Qed.
Lemma lem7137531 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term90 A x s f b) = (term91 A x s f b).
Proof. exact (MK_COMB (@lem7137530 A s f b) (@lem7137527 A x s f b)). Qed.
Lemma lem7137534 {A : Type'} (s : A -> Prop) : (term92 A s) = (term92 A s).
Proof. exact (eq_refl (term92 A s)). Qed.
Lemma lem7137535 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term78 A x s f b) = (term93 A x s f b).
Proof. exact (MK_COMB (@lem7137534 A s) (@lem7137531 A x s f b)). Qed.
Lemma lem7137538 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term94 A s f b) = (term95 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7137535 A x s f b)). Qed.
Lemma lem7137539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137540 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term96 A s f b) = (term97 A s f b).
Proof. exact (MK_COMB (@lem7137539 A) (@lem7137538 A s f b)). Qed.
Lemma lem7137545 {A : Type'} (f : A -> real) (b : real) : (term98 A f b) = (term99 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7137540 A s f b)). Qed.
Lemma lem7137546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7137547 {A : Type'} (f : A -> real) (b : real) : (term100 A f b) = (term101 A f b).
Proof. exact (MK_COMB (@lem7137546 A) (@lem7137545 A f b)). Qed.
Lemma lem7137552 {A : Type'} (b : real) : (term102 A b) = (term103 A b).
Proof. exact (fun_ext (fun f : A -> real => @lem7137547 A f b)). Qed.
Lemma lem7137553 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7137554 {A : Type'} (b : real) : (term104 A b) = (term105 A b).
Proof. exact (MK_COMB (@lem7137553 A) (@lem7137552 A b)). Qed.
Lemma lem7137559 {A : Type'} : (term106 A) = (term107 A).
Proof. exact (fun_ext (fun b : real => @lem7137554 A b)). Qed.
Lemma lem7137560 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7137569 {A : Type'} : (term108 A) = (term109 A).
Proof. exact (MK_COMB (@lem7137560) (@lem7137559 A)). Qed.
Lemma lem7137574 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term38 A s f x b) = (term38 A s f x b).
Proof. exact (eq_refl (term38 A s f x b)). Qed.
Lemma lem7137575 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term70 A s f b) = (term70 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7137574 A s f x b)). Qed.
Lemma lem7137576 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7137577 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term36 A s f b) = (term36 A s f b).
Proof. exact (MK_COMB (@lem7137576 A) (@lem7137575 A s f b)). Qed.
Lemma lem7137580 {A : Type'} (f : A -> real) (x : A) (b : real) : (term84 A f x b) = (term84 A f x b).
Proof. exact (eq_refl (term84 A f x b)). Qed.
Lemma lem7137581 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term86 A x s f b) = (term86 A x s f b).
Proof. exact (MK_COMB (@lem7137580 A f x b) (@lem7137577 A s f b)). Qed.
Lemma lem7137584 {A : Type'} (x : A) (s : A -> Prop) : (term57 A x s) = (term57 A x s).
Proof. exact (eq_refl (term57 A x s)). Qed.
Lemma lem7137585 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term88 A x s f b) = (term88 A x s f b).
Proof. exact (MK_COMB (@lem7137584 A x s) (@lem7137581 A x s f b)). Qed.
Lemma lem7137590 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term45 A s f x b) = (term45 A s f x b).
Proof. exact (eq_refl (term45 A s f x b)). Qed.
Lemma lem7137591 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term110 A s f b) = (term110 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7137590 A s f x b)). Qed.
Lemma lem7137592 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137593 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term37 A s f b) = (term37 A s f b).
Proof. exact (MK_COMB (@lem7137592 A) (@lem7137591 A s f b)). Qed.
Lemma lem7137594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7137595 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term89 A s f b) = (term89 A s f b).
Proof. exact (MK_COMB (@lem7137594) (@lem7137593 A s f b)). Qed.
Lemma lem7137596 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term91 A x s f b) = (term91 A x s f b).
Proof. exact (MK_COMB (@lem7137595 A s f b) (@lem7137585 A x s f b)). Qed.
Lemma lem7137599 {A : Type'} (s : A -> Prop) : (term92 A s) = (term92 A s).
Proof. exact (eq_refl (term92 A s)). Qed.
Lemma lem7137600 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term93 A x s f b) = (term93 A x s f b).
Proof. exact (MK_COMB (@lem7137599 A s) (@lem7137596 A x s f b)). Qed.
Lemma lem7137601 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term95 A s f b) = (term95 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7137600 A x s f b)). Qed.
Lemma lem7137602 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137603 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term97 A s f b) = (term97 A s f b).
Proof. exact (MK_COMB (@lem7137602 A) (@lem7137601 A s f b)). Qed.
Lemma lem7137604 {A : Type'} (f : A -> real) (b : real) : (term99 A f b) = (term99 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7137603 A s f b)). Qed.
Lemma lem7137605 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7137606 {A : Type'} (f : A -> real) (b : real) : (term101 A f b) = (term101 A f b).
Proof. exact (MK_COMB (@lem7137605 A) (@lem7137604 A f b)). Qed.
Lemma lem7137607 {A : Type'} (b : real) : (term103 A b) = (term103 A b).
Proof. exact (fun_ext (fun f : A -> real => @lem7137606 A f b)). Qed.
Lemma lem7137608 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7137609 {A : Type'} (b : real) : (term105 A b) = (term105 A b).
Proof. exact (MK_COMB (@lem7137608 A) (@lem7137607 A b)). Qed.
Lemma lem7137610 {A : Type'} : (term107 A) = (term107 A).
Proof. exact (fun_ext (fun b : real => @lem7137609 A b)). Qed.
Lemma lem7137611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7137612 {A : Type'} : (term109 A) = (term109 A).
Proof. exact (MK_COMB (@lem7137611) (@lem7137610 A)). Qed.
Lemma lem7137663 {A : Type'} : (term108 A) = (term109 A).
Proof. exact (TRANS (@lem7137569 A) (@lem7137612 A)). Qed.
Lemma lem7137664 {A : Type'} : (term109 A) = (term108 A).
Proof. exact (SYM (@lem7137663 A)). Qed.
Lemma lem7137670 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7137671 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term36 A s f b) = (term76 A s f b).
Proof. exact (@lem7137670 (term36 A s f b)). Qed.
Lemma lem7137672 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term76 A s f b) = (term36 A s f b).
Proof. exact (SYM (@lem7137671 A s f b)). Qed.
Lemma lem7137673 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term77 A s f b.
Proof. exact (h1). Qed.
Lemma lem7137748 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7137754 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem7137761 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term111 A s f x b) = (term112 A s f x b).
Proof. exact (@lem17045 (@IN A x s) (term39 A f x b)). Qed.
Lemma lem7137762 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7137763 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term77 A s f b) = (term115 A s f b).
Proof. exact (@lem7137762 A (term70 A s f b)). Qed.
Lemma lem7137764 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term116 A s f b x) = (term38 A s f x b).
Proof. exact (eq_refl (term116 A s f b x)). Qed.
Lemma lem7137765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7137766 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term117 A s f b x) = (term111 A s f x b).
Proof. exact (MK_COMB (@lem7137765) (@lem7137764 A s f x b)). Qed.
Lemma lem7137767 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term117 A s f b x) = (term112 A s f x b).
Proof. exact (TRANS (@lem7137766 A s f x b) (@lem7137761 A s f x b)). Qed.
Lemma lem7137768 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term118 A s f b) = (term119 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7137767 A s f x b)). Qed.
Lemma lem7137769 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137770 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term115 A s f b) = (term120 A s f b).
Proof. exact (MK_COMB (@lem7137769 A) (@lem7137768 A s f b)). Qed.
Lemma lem7137823 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term77 A s f b) = (term120 A s f b).
Proof. exact (TRANS (@lem7137763 A s f b) (@lem7137770 A s f b)). Qed.
Lemma lem7137824 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term120 A s f b.
Proof. exact (EQ_MP (@lem7137823 A s f b) (@lem7137673 A s f b h1)). Qed.
Lemma lem7137855 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7137863 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem7137882 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term112 A s f x b) = (term112 A s f x b).
Proof. exact (eq_refl (term112 A s f x b)). Qed.
Lemma lem7137883 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term119 A s f b) = (term119 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7137882 A s f x b)). Qed.
Lemma lem7137884 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137885 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term120 A s f b) = (term120 A s f b).
Proof. exact (MK_COMB (@lem7137884 A) (@lem7137883 A s f b)). Qed.
Lemma lem7137886 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term120 A s f b.
Proof. exact (EQ_MP (@lem7137885 A s f b) (@lem7137824 A s f b h1)). Qed.
Lemma lem7137907 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7137911 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem7137919 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term112 A s f x b) = (term112 A s f x b).
Proof. exact (eq_refl (term112 A s f x b)). Qed.
Lemma lem7137920 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term119 A s f b) = (term119 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7137919 A s f x b)). Qed.
Lemma lem7137921 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7137923 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term120 A s f b) = (term120 A s f b).
Proof. exact (MK_COMB (@lem7137921 A) (@lem7137920 A s f b)). Qed.
Lemma lem7137924 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term120 A s f b.
Proof. exact (EQ_MP (@lem7137923 A s f b) (@lem7137886 A s f b h1)). Qed.
Lemma lem7137928 {A : Type'} (_95335 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term121 A s f b _95335.
Proof. exact (@lem7137924 A s f b h1 _95335). Qed.
Lemma lem7137929 {A : Type'} (s : A -> Prop) (f : A -> real) (_95335 : A) (b : real) : (term121 A s f b _95335) = (term112 A s f _95335 b).
Proof. exact (eq_refl (term121 A s f b _95335)). Qed.
Lemma lem7137940 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7137942 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem7137948 {A : Type'} (_95335 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term112 A s f _95335 b.
Proof. exact (EQ_MP (@lem7137929 A s f _95335 b) (@lem7137928 A _95335 s f b h1)). Qed.
Lemma lem7137950 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7137951 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term122 A x s.
Proof. exact (fun h0 : term123 A x s => @lem7137950 A x s h1). Qed.
Lemma lem7137953 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7137954 {A : Type'} (x : A) (s : A -> Prop) : (term122 A x s) = (@IN A x s).
Proof. exact (@lem7137953 (@IN A x s)). Qed.
Lemma lem7137955 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem7137954 A x s) (@lem7137951 A x s h1)). Qed.
Lemma lem7137957 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (h1). Qed.
Lemma lem7137958 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term125 A f x b.
Proof. exact (fun h0 : term126 A f x b => @lem7137957 A f x b h1). Qed.
Lemma lem7137960 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7137961 {A : Type'} (f : A -> real) (x : A) (b : real) : (term125 A f x b) = (term39 A f x b).
Proof. exact (@lem7137960 (term39 A f x b)). Qed.
Lemma lem7137962 {A : Type'} (f : A -> real) (x : A) (b : real) (h1 : term39 A f x b) : term39 A f x b.
Proof. exact (EQ_MP (@lem7137961 A f x b) (@lem7137958 A f x b h1)). Qed.
Lemma lem7137964 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7137965 {A : Type'} (s : A -> Prop) (f : A -> real) (_95335 : A) (b : real) : (term112 A s f _95335 b) = (term111 A s f _95335 b).
Proof. exact (@lem7137964 (@IN A _95335 s) (term39 A f _95335 b)). Qed.
Lemma lem7137967 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7137968 {A : Type'} (s : A -> Prop) (f : A -> real) (_95335 : A) (b : real) : (term111 A s f _95335 b) = (term129 A s f _95335 b).
Proof. exact (@lem7137967 (term38 A s f _95335 b)). Qed.
Lemma lem7137969 {A : Type'} (s : A -> Prop) (f : A -> real) (_95335 : A) (b : real) : (term112 A s f _95335 b) = (term129 A s f _95335 b).
Proof. exact (TRANS (@lem7137965 A s f _95335 b) (@lem7137968 A s f _95335 b)). Qed.
Lemma lem7137971 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : @IN A x s) (h2 : term39 A f x b) : term38 A s f x b.
Proof. exact (conj (@lem7137955 A x s h1) (@lem7137962 A f x b h2)). Qed.
Lemma lem7137973 {A : Type'} (_95335 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term129 A s f _95335 b.
Proof. exact (EQ_MP (@lem7137969 A s f _95335 b) (@lem7137948 A _95335 s f b h1)). Qed.
Lemma lem7137974 {A : Type'} (_95335 : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term129 A s f _95335 b.
Proof. exact (@lem7137973 A _95335 s f b h1). Qed.
Lemma lem7137975 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) (h1 : term77 A s f b) : term129 A s f x b.
Proof. exact (@lem7137974 A x s f b h1). Qed.
Lemma lem7137978 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (@lem7137975 A x s f b h1 (@lem7137971 A s f x b h2 h3)). Qed.
Lemma lem7137979 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : term130.
Proof. exact (fun h0 : ~ False => @lem7137978 A s f x b h1 h2 h3). Qed.
Lemma lem7137981 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7137982 : term130 = False.
Proof. exact (@lem7137981 False). Qed.
Lemma lem7137983 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137982) (@lem7137979 A s f x b h1 h2 h3)). Qed.
Lemma lem7137984 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem7137983 A s f x b h1 h2 h3) (fun h4 : False => @lem7137942 A f x b h3)). Qed.
Lemma lem7137985 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137984 A s f x b h1 h2 h3) (@lem7137942 A f x b h3)). Qed.
Lemma lem7137986 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7137985 A s f x b h1 h2 h3) (fun h4 : False => @lem7137940 A x s h2)). Qed.
Lemma lem7137987 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137986 A s f x b h1 h2 h3) (@lem7137940 A x s h2)). Qed.
Lemma lem7137988 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem7137987 A s f x b h1 h2 h3) (fun h4 : False => @lem7137911 A f x b h3)). Qed.
Lemma lem7137989 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137988 A s f x b h1 h2 h3) (@lem7137911 A f x b h3)). Qed.
Lemma lem7137990 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7137989 A s f x b h1 h2 h3) (fun h4 : False => @lem7137907 A x s h2)). Qed.
Lemma lem7137991 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137990 A s f x b h1 h2 h3) (@lem7137907 A x s h2)). Qed.
Lemma lem7137992 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem7137991 A s f x b h1 h2 h3) (fun h4 : False => @lem7137911 A f x b h3)). Qed.
Lemma lem7137993 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137992 A s f x b h1 h2 h3) (@lem7137911 A f x b h3)). Qed.
Lemma lem7137994 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7137993 A s f x b h1 h2 h3) (fun h4 : False => @lem7137907 A x s h2)). Qed.
Lemma lem7137995 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137994 A s f x b h1 h2 h3) (@lem7137907 A x s h2)). Qed.
Lemma lem7137996 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem7137995 A s f x b h1 h2 h3) (fun h4 : False => @lem7137863 A f x b h3)). Qed.
Lemma lem7137997 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137996 A s f x b h1 h2 h3) (@lem7137863 A f x b h3)). Qed.
Lemma lem7137998 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7137997 A s f x b h1 h2 h3) (fun h4 : False => @lem7137855 A x s h2)). Qed.
Lemma lem7137999 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7137998 A s f x b h1 h2 h3) (@lem7137855 A x s h2)). Qed.
Lemma lem7138000 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (term39 A f x b) = False.
Proof. exact (prop_ext (fun h4 : term39 A f x b => @lem7137999 A s f x b h1 h2 h3) (fun h4 : False => @lem7137754 A f x b h3)). Qed.
Lemma lem7138001 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7138000 A s f x b h1 h2 h3) (@lem7137754 A f x b h3)). Qed.
Lemma lem7138002 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7138001 A s f x b h1 h2 h3) (fun h4 : False => @lem7137748 A x s h2)). Qed.
Lemma lem7138003 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7138002 A s f x b h1 h2 h3) (@lem7137748 A x s h2)). Qed.
Lemma lem7138004 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : (term77 A s f b) = False.
Proof. exact (prop_ext (fun h4 : term77 A s f b => @lem7138003 A s f x b h1 h2 h3) (fun h4 : False => @lem7137673 A s f b h1)). Qed.
Lemma lem7138005 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term77 A s f b) (h2 : @IN A x s) (h3 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7138004 A s f x b h1 h2 h3) (@lem7137673 A s f b h1)). Qed.
Lemma lem7138006 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : @IN A x s) (h2 : term39 A f x b) : term76 A s f b.
Proof. exact (fun h0 : term77 A s f b => @lem7138005 A s f x b h0 h1 h2). Qed.
Lemma lem7138007 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : @IN A x s) (h2 : term39 A f x b) : term36 A s f b.
Proof. exact (EQ_MP (@lem7137672 A s f b) (@lem7138006 A s f x b h1 h2)). Qed.
Lemma lem7138008 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term86 A x s f b.
Proof. exact (fun h0 : term39 A f x b => @lem7138007 A s f x b h1 h0). Qed.
Lemma lem7138009 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term88 A x s f b.
Proof. exact (fun h0 : @IN A x s => @lem7138008 A f b x s h0). Qed.
Lemma lem7138010 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term91 A x s f b.
Proof. exact (fun h0 : term37 A s f b => @lem7138009 A x s f b). Qed.
Lemma lem7138011 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term93 A x s f b.
Proof. exact (fun h0 : @FINITE A s => @lem7138010 A x s f b). Qed.
Lemma lem7138016 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : term97 A s f b.
Proof. exact (fun x : A => @lem7138011 A x s f b). Qed.
Lemma lem7138021 {A : Type'} (f : A -> real) (b : real) : term101 A f b.
Proof. exact (fun s : A -> Prop => @lem7138016 A s f b). Qed.
Lemma lem7138026 {A : Type'} (b : real) : term105 A b.
Proof. exact (fun f : A -> real => @lem7138021 A f b). Qed.
Lemma lem7138031 {A : Type'} : term109 A.
Proof. exact (fun b : real => @lem7138026 A b). Qed.
Lemma lem7138032 {A : Type'} : term108 A.
Proof. exact (EQ_MP (@lem7137664 A) (@lem7138031 A)). Qed.
Lemma lem7138033 {A : Type'} (b : real) : term131 A b.
Proof. exact (@lem7138032 A b). Qed.
Lemma lem7138034 {A : Type'} (b : real) : (term131 A b) = (term104 A b).
Proof. exact (eq_refl (term131 A b)). Qed.
Lemma lem7138035 {A : Type'} (b : real) : term104 A b.
Proof. exact (EQ_MP (@lem7138034 A b) (@lem7138033 A b)). Qed.
Lemma lem7138036 {A : Type'} (b : real) (f : A -> real) : term132 A b f.
Proof. exact (@lem7138035 A b f). Qed.
Lemma lem7138037 {A : Type'} (f : A -> real) (b : real) : (term132 A b f) = (term100 A f b).
Proof. exact (eq_refl (term132 A b f)). Qed.
Lemma lem7138038 {A : Type'} (f : A -> real) (b : real) : term100 A f b.
Proof. exact (EQ_MP (@lem7138037 A f b) (@lem7138036 A b f)). Qed.
Lemma lem7138039 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) : term133 A f b s.
Proof. exact (@lem7138038 A f b s). Qed.
Lemma lem7138040 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term133 A f b s) = (term96 A s f b).
Proof. exact (eq_refl (term133 A f b s)). Qed.
Lemma lem7138041 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : term96 A s f b.
Proof. exact (EQ_MP (@lem7138040 A s f b) (@lem7138039 A f b s)). Qed.
Lemma lem7138042 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) : term134 A s f b x.
Proof. exact (@lem7138041 A s f b x). Qed.
Lemma lem7138043 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term134 A s f b x) = (term78 A x s f b).
Proof. exact (eq_refl (term134 A s f b x)). Qed.
Lemma lem7138044 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term78 A x s f b.
Proof. exact (EQ_MP (@lem7138043 A x s f b) (@lem7138042 A s f b x)). Qed.
Lemma lem7138046 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : term78 A x s f b.
Proof. exact (@lem7137434 A x s f b (@lem7138044 A x s f b)). Qed.
Lemma lem7138047 {A : Type'} (x : A) (f : A -> real) (b : real) (s : A -> Prop) (h1 : @FINITE A s) : term90 A x s f b.
Proof. exact (@lem7138046 A x s f b (@lem7137204 A s h1)). Qed.
Lemma lem7138048 {A : Type'} (x : A) (f : A -> real) (b : real) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) : term87 A x s f b.
Proof. exact (@lem7138047 A x f b s h2 (@lem7137206 A s f b h1)). Qed.
Lemma lem7138049 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) : term85 A x s f b.
Proof. exact (@lem7138048 A x f b s h1 h2 (@lem7137209 A x s h3)). Qed.
Lemma lem7138050 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term76 A s f b.
Proof. exact (@lem7138049 A f b x s h1 h2 h3 (@lem7137208 A f x b h4)). Qed.
Lemma lem7138051 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term77 A s f b) (h4 : @IN A x s) (h5 : term39 A f x b) : False.
Proof. exact (@lem7138050 A s f x b h1 h2 h4 h5 (@lem7137418 A s f b h3)). Qed.
Lemma lem7138052 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term77 A s f b) (h4 : @IN A x s) (h5 : term39 A f x b) : (term77 A s f b) = False.
Proof. exact (prop_ext (fun h6 : term77 A s f b => @lem7138051 A s f x b h1 h2 h3 h4 h5) (fun h6 : False => @lem7137418 A s f b h3)). Qed.
Lemma lem7138053 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term77 A s f b) (h4 : @IN A x s) (h5 : term39 A f x b) : False.
Proof. exact (EQ_MP (@lem7138052 A s f x b h1 h2 h3 h4 h5) (@lem7137418 A s f b h3)). Qed.
Lemma lem7138054 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term76 A s f b.
Proof. exact (fun h0 : term77 A s f b => @lem7138053 A s f x b h1 h2 h0 h3 h4). Qed.
Lemma lem7138055 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term36 A s f b.
Proof. exact (EQ_MP (@lem7137417 A s f b) (@lem7138054 A s f x b h1 h2 h3 h4)). Qed.
Lemma lem7138056 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term74 A s f b.
Proof. exact (EQ_MP (@lem7137413 A f b s h1 h2) (@lem7138055 A s f x b h1 h2 h3 h4)). Qed.
Lemma lem7138057 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term135 A f s b.
Proof. exact (@lem7137216 A f s b (@lem7138056 A s f x b h1 h2 h3 h4)). Qed.
Lemma lem7138058 (x : real) : term136 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem7138059 (x : real) : (term136 x) = (real_le x x).
Proof. exact (eq_refl (term136 x)). Qed.
Lemma lem7138060 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem7138059 x) (@lem7138058 x)). Qed.
Lemma lem7138061 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem7138063 {_132484 : Type'} (c : real) : term137 _132484 c.
Proof. exact (@lem7085323 _132484 c). Qed.
Lemma lem7138064 {_132484 : Type'} (c : real) : (term137 _132484 c) = (term138 _132484 c).
Proof. exact (eq_refl (term137 _132484 c)). Qed.
Lemma lem7138065 {_132484 : Type'} (c : real) : term138 _132484 c.
Proof. exact (EQ_MP (@lem7138064 _132484 c) (@lem7138063 _132484 c)). Qed.
Lemma lem7138066 {_132484 : Type'} (c : real) (s : _132484 -> Prop) : term139 _132484 c s.
Proof. exact (@lem7138065 _132484 c s). Qed.
Lemma lem7138067 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : (term139 _132484 c s) = (term140 _132484 s c).
Proof. exact (eq_refl (term139 _132484 c s)). Qed.
Lemma lem7138068 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term140 _132484 s c.
Proof. exact (EQ_MP (@lem7138067 _132484 s c) (@lem7138066 _132484 c s)). Qed.
Lemma lem7138069 {_132484 : Type'} (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : @FINITE _132484 s.
Proof. exact (h1). Qed.
Lemma lem7138070 {_132484 : Type'} (c : real) (s : _132484 -> Prop) (h1 : @FINITE _132484 s) : (term141 _132484 s c) = (term41 _132484 s c).
Proof. exact (@lem7138068 _132484 s c (@lem7138069 _132484 s h1)). Qed.
Lemma lem7138076 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7138097 {_132484 : Type'} (s : _132484 -> Prop) (c : real) : term140 _132484 s c.
Proof. exact (fun h0 : @FINITE _132484 s => @lem7138070 _132484 c s h0). Qed.
Lemma lem7138098 {A : Type'} (s : A -> Prop) (c : real) : term140 A s c.
Proof. exact (@lem7138097 A s c). Qed.
Lemma lem7138099 {A : Type'} (s : A -> Prop) (b : real) : term140 A s b.
Proof. exact (@lem7138098 A s b). Qed.
Lemma lem7138101 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7138076 A s) (@lem7137204 A s h1)). Qed.
Lemma lem7138102 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7138101 A s h1)). Qed.
Lemma lem7138103 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7138102 A s h1) (@lem0)). Qed.
Lemma lem7138104 {A : Type'} (b : real) (s : A -> Prop) (h1 : @FINITE A s) : (term141 A s b) = (term41 A s b).
Proof. exact (@lem7138099 A s b (@lem7138103 A s h1)). Qed.
Lemma lem7138105 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7138106 {A : Type'} (b : real) (s : A -> Prop) (h1 : @FINITE A s) : (term142 A s b) = (term143 A s b).
Proof. exact (MK_COMB (@lem7138105) (@lem7138104 A b s h1)). Qed.
Lemma lem7138107 {A : Type'} (s : A -> Prop) (b : real) : (term41 A s b) = (term41 A s b).
Proof. exact (eq_refl (term41 A s b)). Qed.
Lemma lem7138108 {A : Type'} (b : real) (s : A -> Prop) (h1 : @FINITE A s) : (term144 A s b) = (term145 A s b).
Proof. exact (MK_COMB (@lem7138106 A b s h1) (@lem7138107 A s b)). Qed.
Lemma lem7138110 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem7138061 x) (@lem7138060 x)). Qed.
Lemma lem7138111 {A : Type'} (s : A -> Prop) (b : real) : (term145 A s b) = True.
Proof. exact (@lem7138110 (term41 A s b)). Qed.
Lemma lem7138112 {A : Type'} (b : real) (s : A -> Prop) (h1 : @FINITE A s) : (term144 A s b) = True.
Proof. exact (TRANS (@lem7138108 A b s h1) (@lem7138111 A s b)). Qed.
Lemma lem7138113 {A : Type'} (b : real) (s : A -> Prop) (h1 : @FINITE A s) : True = (term144 A s b).
Proof. exact (SYM (@lem7138112 A b s h1)). Qed.
Lemma lem7138114 {A : Type'} (b : real) (s : A -> Prop) (h1 : @FINITE A s) : term144 A s b.
Proof. exact (EQ_MP (@lem7138113 A b s h1) (@lem0)). Qed.
Lemma lem7138115 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term146 A f s b.
Proof. exact (conj (@lem7138057 A s f x b h1 h2 h3 h4) (@lem7138114 A b s h2)). Qed.
Lemma lem7138116 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term147 A f s b.
Proof. exact (ex_intro (term148 A f s b) (term141 A s b) (@lem7138115 A s f x b h1 h2 h3 h4)). Qed.
Lemma lem7138117 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term149 A f s b.
Proof. exact (@lem7137212 A f s b (@lem7138116 A s f x b h1 h2 h3 h4)). Qed.
Lemma lem7138118 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term34 A s f b) : term35 A s f b.
Proof. exact (proj2 (@lem7137202 A s f b h1)). Qed.
Lemma lem7138119 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term34 A s f b) : @FINITE A s.
Proof. exact (proj1 (@lem7137202 A s f b h1)). Qed.
Lemma lem7138120 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term35 A s f b) : term36 A s f b.
Proof. exact (proj2 (@lem7137203 A s f b h1)). Qed.
Lemma lem7138121 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term35 A s f b) : term37 A s f b.
Proof. exact (proj1 (@lem7137203 A s f b h1)). Qed.
Lemma lem7138122 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term38 A s f x b) : term39 A f x b.
Proof. exact (proj2 (@lem7137207 A s f x b h1)). Qed.
Lemma lem7138123 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term38 A s f x b) : @IN A x s.
Proof. exact (proj1 (@lem7137207 A s f x b h1)). Qed.
Lemma lem7138124 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : (term39 A f x b) = (term149 A f s b).
Proof. exact (prop_ext (fun h5 : term39 A f x b => @lem7138117 A s f x b h1 h2 h3 h4) (fun h5 : term149 A f s b => @lem7137208 A f x b h4)). Qed.
Lemma lem7138125 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138124 A s f x b h1 h2 h3 h4) (@lem7137208 A f x b h4)). Qed.
Lemma lem7138126 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : (@IN A x s) = (term149 A f s b).
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem7138125 A s f x b h1 h2 h3 h4) (fun h5 : term149 A f s b => @lem7137209 A x s h3)). Qed.
Lemma lem7138127 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : @IN A x s) (h4 : term39 A f x b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138126 A s f x b h1 h2 h3 h4) (@lem7137209 A x s h3)). Qed.
Lemma lem7138128 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) (h4 : @IN A x s) : (term39 A f x b) = (term149 A f s b).
Proof. exact (prop_ext (fun h5 : term39 A f x b => @lem7138127 A s f x b h1 h2 h4 h5) (fun h5 : term149 A f s b => @lem7138122 A s f x b h3)). Qed.
Lemma lem7138129 {A : Type'} (f : A -> real) (b : real) (x : A) (s : A -> Prop) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) (h4 : @IN A x s) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138128 A f b x s h1 h2 h3 h4) (@lem7138122 A s f x b h3)). Qed.
Lemma lem7138130 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) : (@IN A x s) = (term149 A f s b).
Proof. exact (prop_ext (fun h4 : @IN A x s => @lem7138129 A f b x s h1 h2 h3 h4) (fun h4 : term149 A f s b => @lem7138123 A s f x b h3)). Qed.
Lemma lem7138131 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term38 A s f x b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138130 A s f x b h1 h2 h3) (@lem7138123 A s f x b h3)). Qed.
Lemma lem7138132 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term37 A s f b) (h2 : term36 A s f b) (h3 : @FINITE A s) : term149 A f s b.
Proof. exact (ex_elim (@lem7137205 A s f b h2) (fun x : A => fun h0 : term70 A s f b x => @lem7138131 A s f x b h1 h3 h0)). Qed.
Lemma lem7138133 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term37 A s f b) (h2 : term36 A s f b) (h3 : @FINITE A s) : (term37 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h4 : term37 A s f b => @lem7138132 A f b s h1 h2 h3) (fun h4 : term149 A f s b => @lem7137206 A s f b h1)). Qed.
Lemma lem7138134 {A : Type'} (f : A -> real) (b : real) (s : A -> Prop) (h1 : term37 A s f b) (h2 : term36 A s f b) (h3 : @FINITE A s) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138133 A f b s h1 h2 h3) (@lem7137206 A s f b h1)). Qed.
Lemma lem7138135 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term35 A s f b) : (term36 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h4 : term36 A s f b => @lem7138134 A f b s h1 h4 h2) (fun h4 : term149 A f s b => @lem7138120 A s f b h3)). Qed.
Lemma lem7138136 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term37 A s f b) (h2 : @FINITE A s) (h3 : term35 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138135 A s f b h1 h2 h3) (@lem7138120 A s f b h3)). Qed.
Lemma lem7138137 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term35 A s f b) : (term37 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h3 : term37 A s f b => @lem7138136 A s f b h3 h1 h2) (fun h3 : term149 A f s b => @lem7138121 A s f b h2)). Qed.
Lemma lem7138138 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term35 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138137 A s f b h1 h2) (@lem7138121 A s f b h2)). Qed.
Lemma lem7138139 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term35 A s f b) : (@FINITE A s) = (term149 A f s b).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7138138 A s f b h1 h2) (fun h3 : term149 A f s b => @lem7137204 A s h1)). Qed.
Lemma lem7138140 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term35 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138139 A s f b h1 h2) (@lem7137204 A s h1)). Qed.
Lemma lem7138141 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term34 A s f b) : (term35 A s f b) = (term149 A f s b).
Proof. exact (prop_ext (fun h3 : term35 A s f b => @lem7138140 A s f b h1 h3) (fun h3 : term149 A f s b => @lem7138118 A s f b h2)). Qed.
Lemma lem7138142 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : @FINITE A s) (h2 : term34 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138141 A s f b h1 h2) (@lem7138118 A s f b h2)). Qed.
Lemma lem7138143 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term34 A s f b) : (@FINITE A s) = (term149 A f s b).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7138142 A s f b h2 h1) (fun h2 : term149 A f s b => @lem7138119 A s f b h1)). Qed.
Lemma lem7138144 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (h1 : term34 A s f b) : term149 A f s b.
Proof. exact (EQ_MP (@lem7138143 A s f b h1) (@lem7138119 A s f b h1)). Qed.
Lemma lem7138145 {A : Type'} (f : A -> real) (s : A -> Prop) (b : real) : term150 A f s b.
Proof. exact (fun h0 : term34 A s f b => @lem7138144 A s f b h0). Qed.
Lemma lem7138150 {A : Type'} (f : A -> real) (s : A -> Prop) : term151 A f s.
Proof. exact (fun b : real => @lem7138145 A f s b). Qed.
Lemma lem7138155 {A : Type'} (s : A -> Prop) : term152 A s.
Proof. exact (fun f : A -> real => @lem7138150 A f s). Qed.
Lemma lem7138160 {A : Type'} : term153 A.
Proof. exact (fun s : A -> Prop => @lem7138155 A s). Qed.
