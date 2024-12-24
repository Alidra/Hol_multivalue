Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_RESTRICT_term_abbrevs.
Require Import SUM_EQ_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7132220 {_132349 : Type'} (h1 : term0 _132349) : term0 _132349.
Proof. exact (h1). Qed.
Lemma lem7132221 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term1 _132349 f.
Proof. exact (@lem7132220 _132349 h1 f). Qed.
Lemma lem7132222 {_132349 : Type'} (f : _132349 -> real) : (term1 _132349 f) = (term2 _132349 f).
Proof. exact (eq_refl (term1 _132349 f)). Qed.
Lemma lem7132223 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term2 _132349 f.
Proof. exact (EQ_MP (@lem7132222 _132349 f) (@lem7132221 _132349 f h1)). Qed.
Lemma lem7132224 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term0 _132349) : term3 _132349 f g.
Proof. exact (@lem7132223 _132349 f h1 g). Qed.
Lemma lem7132225 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term3 _132349 f g) = (term4 _132349 f g).
Proof. exact (eq_refl (term3 _132349 f g)). Qed.
Lemma lem7132226 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (h1 : term0 _132349) : term4 _132349 f g.
Proof. exact (EQ_MP (@lem7132225 _132349 f g) (@lem7132224 _132349 f g h1)). Qed.
Lemma lem7132227 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (s : _132349 -> Prop) (h1 : term0 _132349) : term5 _132349 f g s.
Proof. exact (@lem7132226 _132349 f g h1 s). Qed.
Lemma lem7132228 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term5 _132349 f g s) = (term6 _132349 f s g).
Proof. exact (eq_refl (term5 _132349 f g s)). Qed.
Lemma lem7132229 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term0 _132349) : term6 _132349 f s g.
Proof. exact (EQ_MP (@lem7132228 _132349 f s g) (@lem7132227 _132349 f g s h1)). Qed.
Lemma lem7132230 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) : term7 _132349 s f g.
Proof. exact (h1). Qed.
Lemma lem7132231 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) (h2 : term0 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7132229 _132349 f s g h2 (@lem7132230 _132349 s f g h1)). Qed.
Lemma lem7132232 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) : term8 _132349 f s g.
Proof. exact (fun h0 : term0 _132349 => @lem7132231 _132349 s f g h1 h0). Qed.
Lemma lem7132233 {_132349 : Type'} (h1 : term0 _132349) : term0 _132349.
Proof. exact (h1). Qed.
Lemma lem7132234 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (h1 : term7 _132349 s f g) (h2 : term0 _132349) : (@sum _132349 s f) = (@sum _132349 s g).
Proof. exact (@lem7132232 _132349 s f g h1 (@lem7132233 _132349 h2)). Qed.
Lemma lem7132235 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (h1 : term0 _132349) : term6 _132349 f s g.
Proof. exact (fun h0 : term7 _132349 s f g => @lem7132234 _132349 s f g h0 h1). Qed.
Lemma lem7132236 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (h1 : term0 _132349) : term9 _132349 f s.
Proof. exact (fun g : _132349 -> real => @lem7132235 _132349 f s g h1). Qed.
Lemma lem7132237 {_132349 : Type'} (f : _132349 -> real) (h1 : term0 _132349) : term10 _132349 f.
Proof. exact (fun s : _132349 -> Prop => @lem7132236 _132349 f s h1). Qed.
Lemma lem7132238 {_132349 : Type'} (h1 : term0 _132349) : term11 _132349.
Proof. exact (fun f : _132349 -> real => @lem7132237 _132349 f h1). Qed.
Lemma lem7132239 {_132349 : Type'} : term12 _132349.
Proof. exact (fun h0 : term0 _132349 => @lem7132238 _132349 h0). Qed.
Lemma lem7132240 {_132349 : Type'} : term11 _132349.
Proof. exact (@lem7132239 _132349 (@lem7081239 _132349)). Qed.
Lemma lem7132241 {_132349 : Type'} (f : _132349 -> real) : term13 _132349 f.
Proof. exact (@lem7132240 _132349 f). Qed.
Lemma lem7132242 {_132349 : Type'} (f : _132349 -> real) : (term13 _132349 f) = (term10 _132349 f).
Proof. exact (eq_refl (term13 _132349 f)). Qed.
Lemma lem7132243 {_132349 : Type'} (f : _132349 -> real) : term10 _132349 f.
Proof. exact (EQ_MP (@lem7132242 _132349 f) (@lem7132241 _132349 f)). Qed.
Lemma lem7132244 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term14 _132349 f s.
Proof. exact (@lem7132243 _132349 f s). Qed.
Lemma lem7132245 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : (term14 _132349 f s) = (term9 _132349 f s).
Proof. exact (eq_refl (term14 _132349 f s)). Qed.
Lemma lem7132246 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) : term9 _132349 f s.
Proof. exact (EQ_MP (@lem7132245 _132349 f s) (@lem7132244 _132349 f s)). Qed.
Lemma lem7132247 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term15 _132349 f s g.
Proof. exact (@lem7132246 _132349 f s g). Qed.
Lemma lem7132248 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term15 _132349 f s g) = (term6 _132349 f s g).
Proof. exact (eq_refl (term15 _132349 f s g)). Qed.
Lemma lem7132252 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term6 _132349 f s g.
Proof. exact (EQ_MP (@lem7132248 _132349 f s g) (@lem7132247 _132349 f s g)). Qed.
Lemma lem7132253 {_133404 : Type'} (f : _133404 -> real) (s : _133404 -> Prop) (g : _133404 -> real) : term6 _133404 f s g.
Proof. exact (@lem7132252 _133404 f s g). Qed.
Lemma lem7132254 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : term16 _133404 s f.
Proof. exact (@lem7132253 _133404 (term17 _133404 s f) s f). Qed.
Lemma lem7132264 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term18 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7132265 (p : Prop) (q : Prop) (p' : Prop) : term19 p q p'.
Proof. exact (fun q' : Prop => @lem7132264 p q p' q'). Qed.
Lemma lem7132266 (p : Prop) (q : Prop) : term20 p q.
Proof. exact (fun p' : Prop => @lem7132265 p q p'). Qed.
Lemma lem7132267 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : term21 _133404 s f x.
Proof. exact (@lem7132266 (@IN _133404 x s) ((term22 _133404 s f x) = (f x))). Qed.
Lemma lem7132268 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (p' : Prop) : term23 _133404 s f x p'.
Proof. exact (@lem7132267 _133404 s f x p'). Qed.
Lemma lem7132269 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (p' : Prop) : (term23 _133404 s f x p') = (term24 _133404 s f x p').
Proof. exact (eq_refl (term23 _133404 s f x p')). Qed.
Lemma lem7132270 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (p' : Prop) : term24 _133404 s f x p'.
Proof. exact (EQ_MP (@lem7132269 _133404 s f x p') (@lem7132268 _133404 s f x p')). Qed.
Lemma lem7132271 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (p' : Prop) (q' : Prop) : term25 _133404 s f x p' q'.
Proof. exact (@lem7132270 _133404 s f x p' q'). Qed.
Lemma lem7132272 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (p' : Prop) (q' : Prop) : (term25 _133404 s f x p' q') = (term26 _133404 s f x p' q').
Proof. exact (eq_refl (term25 _133404 s f x p' q')). Qed.
Lemma lem7132273 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (p' : Prop) (q' : Prop) : term26 _133404 s f x p' q'.
Proof. exact (EQ_MP (@lem7132272 _133404 s f x p' q') (@lem7132271 _133404 s f x p' q')). Qed.
Lemma lem7132274 {_133404 : Type'} (x : _133404) (s : _133404 -> Prop) : (@IN _133404 x s) = (@IN _133404 x s).
Proof. exact (eq_refl (@IN _133404 x s)). Qed.
Lemma lem7132275 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (q' : Prop) : term27 _133404 f x s q'.
Proof. exact (@lem7132273 _133404 s f x (@IN _133404 x s) q'). Qed.
Lemma lem7132276 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (q' : Prop) : term28 _133404 f x s q'.
Proof. exact (@lem7132275 _133404 f x s q' (@lem7132274 _133404 x s)). Qed.
Lemma lem7132277 {_133404 : Type'} (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : @IN _133404 x s.
Proof. exact (h1). Qed.
Lemma lem7132278 {_133404 : Type'} (x : _133404) (s : _133404 -> Prop) : (@IN _133404 x s) = ((@IN _133404 x s) = True).
Proof. exact (@lem7 (@IN _133404 x s)). Qed.
Lemma lem7132283 {A B : Type'} (f : A -> B) (y : A) : (term29 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7132284 {_133404 : Type'} (f : _133404 -> real) (y : _133404) : (term30 _133404 f y) = (f y).
Proof. exact (@lem7132283 _133404 real f y). Qed.
Lemma lem7132285 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : (term31 _133404 s f x) = (term22 _133404 s f x).
Proof. exact (@lem7132284 _133404 (term17 _133404 s f) x). Qed.
Lemma lem7132286 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : (term22 _133404 s f x) = (term32 _133404 s f x).
Proof. exact (eq_refl (term22 _133404 s f x)). Qed.
Lemma lem7132287 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : (term33 _133404 s f) = (term17 _133404 s f).
Proof. exact (fun_ext (fun x : _133404 => @lem7132286 _133404 s f x)). Qed.
Lemma lem7132288 {_133404 : Type'} (x : _133404) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7132289 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : (term31 _133404 s f x) = (term22 _133404 s f x).
Proof. exact (MK_COMB (@lem7132287 _133404 s f) (@lem7132288 _133404 x)). Qed.
Lemma lem7132290 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7132291 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : (term34 _133404 s f x) = (term35 _133404 s f x).
Proof. exact (MK_COMB (@lem7132290) (@lem7132289 _133404 s f x)). Qed.
Lemma lem7132292 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : (term22 _133404 s f x) = (term32 _133404 s f x).
Proof. exact (eq_refl (term22 _133404 s f x)). Qed.
Lemma lem7132293 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : ((term31 _133404 s f x) = (term22 _133404 s f x)) = ((term22 _133404 s f x) = (term32 _133404 s f x)).
Proof. exact (MK_COMB (@lem7132291 _133404 s f x) (@lem7132292 _133404 s f x)). Qed.
Lemma lem7132294 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : (term22 _133404 s f x) = (term32 _133404 s f x).
Proof. exact (EQ_MP (@lem7132293 _133404 s f x) (@lem7132285 _133404 s f x)). Qed.
Lemma lem7132296 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term36 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7132297 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term37 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7132296 _2963 g t e g' t' e'). Qed.
Lemma lem7132298 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term38 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7132297 _2963 g t e g' t'). Qed.
Lemma lem7132299 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term39 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7132298 _2963 g t e g'). Qed.
Lemma lem7132300 (g : Prop) (t : real) (e : real) : term40 g t e.
Proof. exact (@lem7132299 real g t e). Qed.
Lemma lem7132301 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : term41 _133404 s f x.
Proof. exact (@lem7132300 (@IN _133404 x s) (f x) term42). Qed.
Lemma lem7132302 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) : term43 _133404 s f x g'.
Proof. exact (@lem7132301 _133404 s f x g'). Qed.
Lemma lem7132303 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) : (term43 _133404 s f x g') = (term44 _133404 s f x g').
Proof. exact (eq_refl (term43 _133404 s f x g')). Qed.
Lemma lem7132304 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) : term44 _133404 s f x g'.
Proof. exact (EQ_MP (@lem7132303 _133404 s f x g') (@lem7132302 _133404 s f x g')). Qed.
Lemma lem7132305 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) (t' : real) : term45 _133404 s f x g' t'.
Proof. exact (@lem7132304 _133404 s f x g' t'). Qed.
Lemma lem7132306 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) (t' : real) : (term45 _133404 s f x g' t') = (term46 _133404 s f x g' t').
Proof. exact (eq_refl (term45 _133404 s f x g' t')). Qed.
Lemma lem7132307 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) (t' : real) : term46 _133404 s f x g' t'.
Proof. exact (EQ_MP (@lem7132306 _133404 s f x g' t') (@lem7132305 _133404 s f x g' t')). Qed.
Lemma lem7132308 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) (t' : real) (e' : real) : term47 _133404 s f x g' t' e'.
Proof. exact (@lem7132307 _133404 s f x g' t' e'). Qed.
Lemma lem7132309 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) (t' : real) (e' : real) : (term47 _133404 s f x g' t' e') = (term48 _133404 s f x g' t' e').
Proof. exact (eq_refl (term47 _133404 s f x g' t' e')). Qed.
Lemma lem7132310 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (g' : Prop) (t' : real) (e' : real) : term48 _133404 s f x g' t' e'.
Proof. exact (EQ_MP (@lem7132309 _133404 s f x g' t' e') (@lem7132308 _133404 s f x g' t' e')). Qed.
Lemma lem7132312 {_133404 : Type'} (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : (@IN _133404 x s) = True.
Proof. exact (EQ_MP (@lem7132278 _133404 x s) (@lem7132277 _133404 x s h1)). Qed.
Lemma lem7132313 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) (t' : real) (e' : real) : term49 _133404 s f x t' e'.
Proof. exact (@lem7132310 _133404 s f x True t' e'). Qed.
Lemma lem7132314 {_133404 : Type'} (f : _133404 -> real) (t' : real) (e' : real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : term50 _133404 s f x t' e'.
Proof. exact (@lem7132313 _133404 s f x t' e' (@lem7132312 _133404 x s h1)). Qed.
Lemma lem7132320 {_133404 : Type'} (f : _133404 -> real) (x : _133404) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7132321 {_133404 : Type'} (f : _133404 -> real) (x : _133404) : term51 _133404 f x.
Proof. exact (fun h0 : True => @lem7132320 _133404 f x). Qed.
Lemma lem7132322 {_133404 : Type'} (f : _133404 -> real) (e' : real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : term52 _133404 s f x e'.
Proof. exact (@lem7132314 _133404 f (f x) e' x s h1). Qed.
Lemma lem7132323 {_133404 : Type'} (f : _133404 -> real) (e' : real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : term53 _133404 s f x e'.
Proof. exact (@lem7132322 _133404 f e' x s h1 (@lem7132321 _133404 f x)). Qed.
Lemma lem7132327 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem7132328 : term54.
Proof. exact (fun h0 : ~ True => @lem7132327). Qed.
Lemma lem7132329 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : term55 _133404 s f x.
Proof. exact (@lem7132323 _133404 f term42 x s h1). Qed.
Lemma lem7132330 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : (term32 _133404 s f x) = (term56 _133404 f x).
Proof. exact (@lem7132329 _133404 f x s h1 (@lem7132328)). Qed.
Lemma lem7132332 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7132333 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7132332 real t2 t1). Qed.
Lemma lem7132334 {_133404 : Type'} (f : _133404 -> real) (x : _133404) : (term56 _133404 f x) = (f x).
Proof. exact (@lem7132333 term42 (f x)). Qed.
Lemma lem7132335 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : (term32 _133404 s f x) = (f x).
Proof. exact (TRANS (@lem7132330 _133404 f x s h1) (@lem7132334 _133404 f x)). Qed.
Lemma lem7132336 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : (term22 _133404 s f x) = (f x).
Proof. exact (TRANS (@lem7132294 _133404 s f x) (@lem7132335 _133404 f x s h1)). Qed.
Lemma lem7132337 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7132338 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : (term35 _133404 s f x) = (term57 _133404 f x).
Proof. exact (MK_COMB (@lem7132337) (@lem7132336 _133404 f x s h1)). Qed.
Lemma lem7132339 {_133404 : Type'} (f : _133404 -> real) (x : _133404) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7132340 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : ((term22 _133404 s f x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem7132338 _133404 f x s h1) (@lem7132339 _133404 f x)). Qed.
Lemma lem7132342 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7132343 (x : real) : (x = x) = True.
Proof. exact (@lem7132342 real x). Qed.
Lemma lem7132344 {_133404 : Type'} (f : _133404 -> real) (x : _133404) : ((f x) = (f x)) = True.
Proof. exact (@lem7132343 (f x)). Qed.
Lemma lem7132345 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) (h1 : @IN _133404 x s) : ((term22 _133404 s f x) = (f x)) = True.
Proof. exact (TRANS (@lem7132340 _133404 f x s h1) (@lem7132344 _133404 f x)). Qed.
Lemma lem7132346 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : term58 _133404 s f x.
Proof. exact (fun h0 : @IN _133404 x s => @lem7132345 _133404 f x s h0). Qed.
Lemma lem7132347 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) : term59 _133404 f x s.
Proof. exact (@lem7132276 _133404 f x s True). Qed.
Lemma lem7132348 {_133404 : Type'} (f : _133404 -> real) (x : _133404) (s : _133404 -> Prop) : (term60 _133404 s f x) = (term61 _133404 x s).
Proof. exact (@lem7132347 _133404 f x s (@lem7132346 _133404 s f x)). Qed.
Lemma lem7132350 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7132351 {_133404 : Type'} (x : _133404) (s : _133404 -> Prop) : (term61 _133404 x s) = True.
Proof. exact (@lem7132350 (@IN _133404 x s)). Qed.
Lemma lem7132352 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) (x : _133404) : (term60 _133404 s f x) = True.
Proof. exact (TRANS (@lem7132348 _133404 f x s) (@lem7132351 _133404 x s)). Qed.
Lemma lem7132353 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : (term62 _133404 s f) = (term63 _133404).
Proof. exact (fun_ext (fun x : _133404 => @lem7132352 _133404 s f x)). Qed.
Lemma lem7132354 {_133404 : Type'} : (@all _133404) = (@all _133404).
Proof. exact (eq_refl (@all _133404)). Qed.
Lemma lem7132355 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : (term64 _133404 s f) = (term65 _133404).
Proof. exact (MK_COMB (@lem7132354 _133404) (@lem7132353 _133404 s f)). Qed.
Lemma lem7132357 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7132358 {_133404 : Type'} (t : Prop) : (term66 _133404 t) = t.
Proof. exact (@lem7132357 _133404 t). Qed.
Lemma lem7132359 {_133404 : Type'} : (term65 _133404) = True.
Proof. exact (@lem7132358 _133404 True). Qed.
Lemma lem7132360 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : (term64 _133404 s f) = True.
Proof. exact (TRANS (@lem7132355 _133404 s f) (@lem7132359 _133404)). Qed.
Lemma lem7132361 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : True = (term64 _133404 s f).
Proof. exact (SYM (@lem7132360 _133404 s f)). Qed.
Lemma lem7132362 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : term64 _133404 s f.
Proof. exact (EQ_MP (@lem7132361 _133404 s f) (@lem0)). Qed.
Lemma lem7132363 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : (term67 _133404 s f) = (@sum _133404 s f).
Proof. exact (@lem7132254 _133404 s f (@lem7132362 _133404 s f)). Qed.
Lemma lem7132364 {_133404 : Type'} (s : _133404 -> Prop) (f : _133404 -> real) : term68 _133404 s f.
Proof. exact (fun h0 : @FINITE _133404 s => @lem7132363 _133404 s f). Qed.
Lemma lem7132369 {_133404 : Type'} (f : _133404 -> real) : term69 _133404 f.
Proof. exact (fun s : _133404 -> Prop => @lem7132364 _133404 s f). Qed.
Lemma lem7132374 {_133404 : Type'} : term70 _133404.
Proof. exact (fun f : _133404 -> real => @lem7132369 _133404 f). Qed.
