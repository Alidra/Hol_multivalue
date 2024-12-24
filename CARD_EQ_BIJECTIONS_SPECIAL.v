Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_EQ_BIJECTIONS_SPECIAL_term_abbrevs.
Require Import CARD_DELETE_spec.
Require Import CARD_EQ_BIJECTIONS_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_DELETE_spec.
Require Import IN_DELETE_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5073218 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5073219 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5073220 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5073219 t1) (@lem5073218 t1)). Qed.
Lemma lem5073221 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5073220 t1 t2). Qed.
Lemma lem5073222 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5073223 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5073222 t1 t2) (@lem5073221 t1 t2)). Qed.
Lemma lem5073224 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5073223 t1 t2 t3). Qed.
Lemma lem5073225 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5073226 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5073225 t1 t2 t3) (@lem5073224 t1 t2 t3)). Qed.
Lemma lem5073227 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5073226 t1 t2 t3)). Qed.
Lemma lem5073228 {A B : Type'} : term7 A B.
Proof. exact (@lem5073217 A B). Qed.
Lemma lem5073229 {A B : Type'} (s : A -> Prop) (a : A) : term8 A B s a.
Proof. exact (@lem5073228 A B (@DELETE A s a)). Qed.
Lemma lem5073230 {A B : Type'} (s : A -> Prop) (a : A) : (term8 A B s a) = (term9 A B s a).
Proof. exact (eq_refl (term8 A B s a)). Qed.
Lemma lem5073231 {A B : Type'} (s : A -> Prop) (a : A) : term9 A B s a.
Proof. exact (EQ_MP (@lem5073230 A B s a) (@lem5073229 A B s a)). Qed.
Lemma lem5073232 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) : term10 A B s a t b.
Proof. exact (@lem5073231 A B s a (@DELETE B t b)). Qed.
Lemma lem5073233 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : (term10 A B s a t b) = (term11 A B t b s a).
Proof. exact (eq_refl (term10 A B s a t b)). Qed.
Lemma lem5073234 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : term11 A B t b s a.
Proof. exact (EQ_MP (@lem5073233 A B t b s a) (@lem5073232 A B s a t b)). Qed.
Lemma lem5073235 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term12 A B a s b t) : term12 A B a s b t.
Proof. exact (h1). Qed.
Lemma lem5073236 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term13 A B a s b t) : term13 A B a s b t.
Proof. exact (h1). Qed.
Lemma lem5073237 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5073238 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term14 A B a s b t) : term14 A B a s b t.
Proof. exact (h1). Qed.
Lemma lem5073239 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem5073240 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term15 A B a s b t) : term15 A B a s b t.
Proof. exact (h1). Qed.
Lemma lem5073241 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem5073242 {B : Type'} (b : B) (t : B -> Prop) (h1 : @IN B b t) : @IN B b t.
Proof. exact (h1). Qed.
Lemma lem5073243 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem5073244 {A : Type'} (P : A -> Prop) : term16 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem5073245 {A : Type'} (P : A -> Prop) : (term16 A P) = (term17 A P).
Proof. exact (eq_refl (term16 A P)). Qed.
Lemma lem5073246 {A : Type'} (P : A -> Prop) : term17 A P.
Proof. exact (EQ_MP (@lem5073245 A P) (@lem5073244 A P)). Qed.
Lemma lem5073247 {A : Type'} (P : A -> Prop) (Q : Prop) : term18 A P Q.
Proof. exact (@lem5073246 A P Q). Qed.
Lemma lem5073248 {A : Type'} (P : A -> Prop) (Q : Prop) : (term18 A P Q) = ((term19 A P Q) = (term20 A P Q)).
Proof. exact (eq_refl (term18 A P Q)). Qed.
Lemma lem5073250 {A : Type'} (s : A -> Prop) : term21 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem5073251 {A : Type'} (s : A -> Prop) : (term21 A s) = (term22 A s).
Proof. exact (eq_refl (term21 A s)). Qed.
Lemma lem5073252 {A : Type'} (s : A -> Prop) : term22 A s.
Proof. exact (EQ_MP (@lem5073251 A s) (@lem5073250 A s)). Qed.
Lemma lem5073253 {A : Type'} (s : A -> Prop) (x : A) : term23 A s x.
Proof. exact (@lem5073252 A s x). Qed.
Lemma lem5073254 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term24 A s x).
Proof. exact (eq_refl (term23 A s x)). Qed.
Lemma lem5073255 {A : Type'} (s : A -> Prop) (x : A) : term24 A s x.
Proof. exact (EQ_MP (@lem5073254 A s x) (@lem5073253 A s x)). Qed.
Lemma lem5073256 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term25 A s x y.
Proof. exact (@lem5073255 A s x y). Qed.
Lemma lem5073257 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term25 A s x y) = ((term26 A x s y) = (term27 A s x y)).
Proof. exact (eq_refl (term25 A s x y)). Qed.
Lemma lem5073259 {A : Type'} (x : A) : term28 A x.
Proof. exact (@lem3845383 A x). Qed.
Lemma lem5073260 {A : Type'} (x : A) : (term28 A x) = (term29 A x).
Proof. exact (eq_refl (term28 A x)). Qed.
Lemma lem5073261 {A : Type'} (x : A) : term29 A x.
Proof. exact (EQ_MP (@lem5073260 A x) (@lem5073259 A x)). Qed.
Lemma lem5073262 {A : Type'} (x : A) (s : A -> Prop) : term30 A x s.
Proof. exact (@lem5073261 A x s). Qed.
Lemma lem5073263 {A : Type'} (x : A) (s : A -> Prop) : (term30 A x s) = (term31 A x s).
Proof. exact (eq_refl (term30 A x s)). Qed.
Lemma lem5073264 {A : Type'} (x : A) (s : A -> Prop) : term31 A x s.
Proof. exact (EQ_MP (@lem5073263 A x s) (@lem5073262 A x s)). Qed.
Lemma lem5073265 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5073266 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term32 A s x) = (term33 A x s).
Proof. exact (@lem5073264 A x s (@lem5073265 A s h1)). Qed.
Lemma lem5073272 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem5073273 {A : Type'} (s : A -> Prop) : (term34 A s) = (term35 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem5073274 {A : Type'} (s : A -> Prop) : term35 A s.
Proof. exact (EQ_MP (@lem5073273 A s) (@lem5073272 A s)). Qed.
Lemma lem5073275 {A : Type'} (s : A -> Prop) (x : A) : term36 A s x.
Proof. exact (@lem5073274 A s x). Qed.
Lemma lem5073276 {A : Type'} (x : A) (s : A -> Prop) : (term36 A s x) = ((term37 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term36 A s x)). Qed.
Lemma lem5073278 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5073280 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem5073282 {A : Type'} (a : A) (s : A -> Prop) : (@IN A a s) = ((@IN A a s) = True).
Proof. exact (@lem7 (@IN A a s)). Qed.
Lemma lem5073284 {B : Type'} (b : B) (t : B -> Prop) : (@IN B b t) = ((@IN B b t) = True).
Proof. exact (@lem7 (@IN B b t)). Qed.
Lemma lem5073289 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term38 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5073290 (p : Prop) (q : Prop) (p' : Prop) : term39 p q p'.
Proof. exact (fun q' : Prop => @lem5073289 p q p' q'). Qed.
Lemma lem5073291 (p : Prop) (q : Prop) : term40 p q.
Proof. exact (fun p' : Prop => @lem5073290 p q p'). Qed.
Lemma lem5073292 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : term41 A B b a t s.
Proof. exact (@lem5073291 (term11 A B t b s a) (term42 A B b a t s)). Qed.
Lemma lem5073293 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) (p' : Prop) : term43 A B b a t s p'.
Proof. exact (@lem5073292 A B b a t s p'). Qed.
Lemma lem5073294 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) (p' : Prop) : (term43 A B b a t s p') = (term44 A B b a t s p').
Proof. exact (eq_refl (term43 A B b a t s p')). Qed.
Lemma lem5073295 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) (p' : Prop) : term44 A B b a t s p'.
Proof. exact (EQ_MP (@lem5073294 A B b a t s p') (@lem5073293 A B b a t s p')). Qed.
Lemma lem5073296 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) (p' : Prop) (q' : Prop) : term45 A B b a t s p' q'.
Proof. exact (@lem5073295 A B b a t s p' q'). Qed.
Lemma lem5073297 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term45 A B b a t s p' q') = (term46 A B b a t s p' q').
Proof. exact (eq_refl (term45 A B b a t s p' q')). Qed.
Lemma lem5073298 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) (p' : Prop) (q' : Prop) : term46 A B b a t s p' q'.
Proof. exact (EQ_MP (@lem5073297 A B b a t s p' q') (@lem5073296 A B b a t s p' q')). Qed.
Lemma lem5073302 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term38 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5073303 (p : Prop) (q : Prop) (p' : Prop) : term39 p q p'.
Proof. exact (fun q' : Prop => @lem5073302 p q p' q'). Qed.
Lemma lem5073304 (p : Prop) (q : Prop) : term40 p q.
Proof. exact (fun p' : Prop => @lem5073303 p q p'). Qed.
Lemma lem5073305 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : term47 A B t b s a.
Proof. exact (@lem5073304 (term48 A B s a t b) (term49 A B t b s a)). Qed.
Lemma lem5073306 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (p' : Prop) : term50 A B t b s a p'.
Proof. exact (@lem5073305 A B t b s a p'). Qed.
Lemma lem5073307 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (p' : Prop) : (term50 A B t b s a p') = (term51 A B t b s a p').
Proof. exact (eq_refl (term50 A B t b s a p')). Qed.
Lemma lem5073308 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (p' : Prop) : term51 A B t b s a p'.
Proof. exact (EQ_MP (@lem5073307 A B t b s a p') (@lem5073306 A B t b s a p')). Qed.
Lemma lem5073309 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (p' : Prop) (q' : Prop) : term52 A B t b s a p' q'.
Proof. exact (@lem5073308 A B t b s a p' q'). Qed.
Lemma lem5073310 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (p' : Prop) (q' : Prop) : (term52 A B t b s a p' q') = (term53 A B t b s a p' q').
Proof. exact (eq_refl (term52 A B t b s a p' q')). Qed.
Lemma lem5073311 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (p' : Prop) (q' : Prop) : term53 A B t b s a p' q'.
Proof. exact (EQ_MP (@lem5073310 A B t b s a p' q') (@lem5073309 A B t b s a p' q')). Qed.
Lemma lem5073315 {A : Type'} (x : A) (s : A -> Prop) : (term37 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem5073276 A x s) (@lem5073275 A s x)). Qed.
Lemma lem5073316 {A : Type'} (x : A) (s : A -> Prop) : (term37 A s x) = (@FINITE A s).
Proof. exact (@lem5073315 A x s). Qed.
Lemma lem5073317 {A : Type'} (a : A) (s : A -> Prop) : (term37 A s a) = (@FINITE A s).
Proof. exact (@lem5073316 A a s). Qed.
Lemma lem5073319 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5073278 A s) (@lem5073237 A s h1)). Qed.
Lemma lem5073320 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term37 A s a) = True.
Proof. exact (TRANS (@lem5073317 A a s) (@lem5073319 A s h1)). Qed.
Lemma lem5073321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5073322 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term54 A s a) = (and True).
Proof. exact (MK_COMB (@lem5073321) (@lem5073320 A a s h1)). Qed.
Lemma lem5073326 {A : Type'} (x : A) (s : A -> Prop) : (term37 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem5073276 A x s) (@lem5073275 A s x)). Qed.
Lemma lem5073327 {B : Type'} (x : B) (s : B -> Prop) : (term37 B s x) = (@FINITE B s).
Proof. exact (@lem5073326 B x s). Qed.
Lemma lem5073328 {B : Type'} (b : B) (t : B -> Prop) : (term37 B t b) = (@FINITE B t).
Proof. exact (@lem5073327 B b t). Qed.
Lemma lem5073330 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem5073280 B t) (@lem5073239 B t h1)). Qed.
Lemma lem5073331 {B : Type'} (b : B) (t : B -> Prop) (h1 : @FINITE B t) : (term37 B t b) = True.
Proof. exact (TRANS (@lem5073328 B b t) (@lem5073330 B t h1)). Qed.
Lemma lem5073332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5073333 {B : Type'} (b : B) (t : B -> Prop) (h1 : @FINITE B t) : (term54 B t b) = (and True).
Proof. exact (MK_COMB (@lem5073332) (@lem5073331 B b t h1)). Qed.
Lemma lem5073337 {A : Type'} (x : A) (s : A -> Prop) : term31 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5073266 A x s h0). Qed.
Lemma lem5073338 {A : Type'} (x : A) (s : A -> Prop) : term31 A x s.
Proof. exact (@lem5073337 A x s). Qed.
Lemma lem5073339 {A : Type'} (a : A) (s : A -> Prop) : term31 A a s.
Proof. exact (@lem5073338 A a s). Qed.
Lemma lem5073341 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5073278 A s) (@lem5073237 A s h1)). Qed.
Lemma lem5073342 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem5073341 A s h1)). Qed.
Lemma lem5073343 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem5073342 A s h1) (@lem0)). Qed.
Lemma lem5073344 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term32 A s a) = (term33 A a s).
Proof. exact (@lem5073339 A a s (@lem5073343 A s h1)). Qed.
Lemma lem5073346 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term55 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5073347 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term56 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5073346 _2963 g t e g' t' e'). Qed.
Lemma lem5073348 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term57 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5073347 _2963 g t e g' t'). Qed.
Lemma lem5073349 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term58 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5073348 _2963 g t e g'). Qed.
Lemma lem5073350 (g : Prop) (t : nat) (e : nat) : term59 g t e.
Proof. exact (@lem5073349 nat g t e). Qed.
Lemma lem5073351 {A : Type'} (a : A) (s : A -> Prop) : term60 A a s.
Proof. exact (@lem5073350 (@IN A a s) (term61 A s) (@CARD A s)). Qed.
Lemma lem5073352 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) : term62 A a s g'.
Proof. exact (@lem5073351 A a s g'). Qed.
Lemma lem5073353 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) : (term62 A a s g') = (term63 A a s g').
Proof. exact (eq_refl (term62 A a s g')). Qed.
Lemma lem5073354 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) : term63 A a s g'.
Proof. exact (EQ_MP (@lem5073353 A a s g') (@lem5073352 A a s g')). Qed.
Lemma lem5073355 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term64 A a s g' t'.
Proof. exact (@lem5073354 A a s g' t'). Qed.
Lemma lem5073356 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term64 A a s g' t') = (term65 A a s g' t').
Proof. exact (eq_refl (term64 A a s g' t')). Qed.
Lemma lem5073357 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term65 A a s g' t'.
Proof. exact (EQ_MP (@lem5073356 A a s g' t') (@lem5073355 A a s g' t')). Qed.
Lemma lem5073358 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term66 A a s g' t' e'.
Proof. exact (@lem5073357 A a s g' t' e'). Qed.
Lemma lem5073359 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term66 A a s g' t' e') = (term67 A a s g' t' e').
Proof. exact (eq_refl (term66 A a s g' t' e')). Qed.
Lemma lem5073360 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term67 A a s g' t' e'.
Proof. exact (EQ_MP (@lem5073359 A a s g' t' e') (@lem5073358 A a s g' t' e')). Qed.
Lemma lem5073362 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : (@IN A a s) = True.
Proof. exact (EQ_MP (@lem5073282 A a s) (@lem5073243 A a s h1)). Qed.
Lemma lem5073363 {A : Type'} (a : A) (s : A -> Prop) (t' : nat) (e' : nat) : term68 A a s t' e'.
Proof. exact (@lem5073360 A a s True t' e'). Qed.
Lemma lem5073364 {A : Type'} (t' : nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term69 A a s t' e'.
Proof. exact (@lem5073363 A a s t' e' (@lem5073362 A a s h1)). Qed.
Lemma lem5073371 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem5073372 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem5073373 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term70 A s) = (term70 B t).
Proof. exact (MK_COMB (@lem5073372) (@lem5073371 A B s t h1)). Qed.
Lemma lem5073374 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem5073375 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (term61 A s) = (term61 B t).
Proof. exact (MK_COMB (@lem5073373 A B s t h1) (@lem5073374)). Qed.
Lemma lem5073376 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : term72 A B s t.
Proof. exact (fun h0 : True => @lem5073375 A B s t h1). Qed.
Lemma lem5073377 {A B : Type'} (t : B -> Prop) (e' : nat) (a : A) (s : A -> Prop) (h1 : @IN A a s) : term73 A B a s t e'.
Proof. exact (@lem5073364 A (term61 B t) e' a s h1). Qed.
Lemma lem5073378 {A B : Type'} (e' : nat) (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : (@CARD A s) = (@CARD B t)) (h2 : @IN A a s) : term74 A B a s t e'.
Proof. exact (@lem5073377 A B t e' a s h2 (@lem5073376 A B s t h1)). Qed.
Lemma lem5073383 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : (@CARD A s) = (@CARD B t).
Proof. exact (h1). Qed.
Lemma lem5073384 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : (@CARD A s) = (@CARD B t)) : term75 A B s t.
Proof. exact (fun h0 : ~ True => @lem5073383 A B s t h1). Qed.
Lemma lem5073385 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : (@CARD A s) = (@CARD B t)) (h2 : @IN A a s) : term76 A B a s t.
Proof. exact (@lem5073378 A B (@CARD B t) t a s h1 h2). Qed.
Lemma lem5073386 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : (@CARD A s) = (@CARD B t)) (h2 : @IN A a s) : (term33 A a s) = (term77 B t).
Proof. exact (@lem5073385 A B t a s h1 h2 (@lem5073384 A B s t h1)). Qed.
Lemma lem5073388 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5073389 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem5073388 nat t2 t1). Qed.
Lemma lem5073390 {B : Type'} (t : B -> Prop) : (term77 B t) = (term61 B t).
Proof. exact (@lem5073389 (@CARD B t) (term61 B t)). Qed.
Lemma lem5073391 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : (@CARD A s) = (@CARD B t)) (h2 : @IN A a s) : (term33 A a s) = (term61 B t).
Proof. exact (TRANS (@lem5073386 A B t a s h1 h2) (@lem5073390 B t)). Qed.
Lemma lem5073392 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : (@CARD A s) = (@CARD B t)) (h3 : @IN A a s) : (term32 A s a) = (term61 B t).
Proof. exact (TRANS (@lem5073344 A a s h1) (@lem5073391 A B t a s h2 h3)). Qed.
Lemma lem5073393 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5073394 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : (@CARD A s) = (@CARD B t)) (h3 : @IN A a s) : (term78 A s a) = (term79 B t).
Proof. exact (MK_COMB (@lem5073393) (@lem5073392 A B t a s h1 h2 h3)). Qed.
Lemma lem5073396 {A : Type'} (x : A) (s : A -> Prop) : term31 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5073266 A x s h0). Qed.
Lemma lem5073397 {B : Type'} (x : B) (s : B -> Prop) : term31 B x s.
Proof. exact (@lem5073396 B x s). Qed.
Lemma lem5073398 {B : Type'} (b : B) (t : B -> Prop) : term31 B b t.
Proof. exact (@lem5073397 B b t). Qed.
Lemma lem5073400 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem5073280 B t) (@lem5073239 B t h1)). Qed.
Lemma lem5073401 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem5073400 B t h1)). Qed.
Lemma lem5073402 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem5073401 B t h1) (@lem0)). Qed.
Lemma lem5073403 {B : Type'} (b : B) (t : B -> Prop) (h1 : @FINITE B t) : (term32 B t b) = (term33 B b t).
Proof. exact (@lem5073398 B b t (@lem5073402 B t h1)). Qed.
Lemma lem5073405 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term55 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5073406 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term56 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5073405 _2963 g t e g' t' e'). Qed.
Lemma lem5073407 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term57 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5073406 _2963 g t e g' t'). Qed.
Lemma lem5073408 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term58 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5073407 _2963 g t e g'). Qed.
Lemma lem5073409 (g : Prop) (t : nat) (e : nat) : term59 g t e.
Proof. exact (@lem5073408 nat g t e). Qed.
Lemma lem5073410 {B : Type'} (b : B) (t : B -> Prop) : term60 B b t.
Proof. exact (@lem5073409 (@IN B b t) (term61 B t) (@CARD B t)). Qed.
Lemma lem5073411 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) : term62 B b t g'.
Proof. exact (@lem5073410 B b t g'). Qed.
Lemma lem5073412 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) : (term62 B b t g') = (term63 B b t g').
Proof. exact (eq_refl (term62 B b t g')). Qed.
Lemma lem5073413 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) : term63 B b t g'.
Proof. exact (EQ_MP (@lem5073412 B b t g') (@lem5073411 B b t g')). Qed.
Lemma lem5073414 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) (t' : nat) : term64 B b t g' t'.
Proof. exact (@lem5073413 B b t g' t'). Qed.
Lemma lem5073415 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) (t' : nat) : (term64 B b t g' t') = (term65 B b t g' t').
Proof. exact (eq_refl (term64 B b t g' t')). Qed.
Lemma lem5073416 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) (t' : nat) : term65 B b t g' t'.
Proof. exact (EQ_MP (@lem5073415 B b t g' t') (@lem5073414 B b t g' t')). Qed.
Lemma lem5073417 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term66 B b t g' t' e'.
Proof. exact (@lem5073416 B b t g' t' e'). Qed.
Lemma lem5073418 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term66 B b t g' t' e') = (term67 B b t g' t' e').
Proof. exact (eq_refl (term66 B b t g' t' e')). Qed.
Lemma lem5073419 {B : Type'} (b : B) (t : B -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term67 B b t g' t' e'.
Proof. exact (EQ_MP (@lem5073418 B b t g' t' e') (@lem5073417 B b t g' t' e')). Qed.
Lemma lem5073421 {B : Type'} (b : B) (t : B -> Prop) (h1 : @IN B b t) : (@IN B b t) = True.
Proof. exact (EQ_MP (@lem5073284 B b t) (@lem5073242 B b t h1)). Qed.
Lemma lem5073422 {B : Type'} (b : B) (t : B -> Prop) (t' : nat) (e' : nat) : term68 B b t t' e'.
Proof. exact (@lem5073419 B b t True t' e'). Qed.
Lemma lem5073423 {B : Type'} (t' : nat) (e' : nat) (b : B) (t : B -> Prop) (h1 : @IN B b t) : term69 B b t t' e'.
Proof. exact (@lem5073422 B b t t' e' (@lem5073421 B b t h1)). Qed.
Lemma lem5073429 {B : Type'} (t : B -> Prop) : (term61 B t) = (term61 B t).
Proof. exact (eq_refl (term61 B t)). Qed.
Lemma lem5073430 {B : Type'} (t : B -> Prop) : term80 B t.
Proof. exact (fun h0 : True => @lem5073429 B t). Qed.
Lemma lem5073431 {B : Type'} (e' : nat) (b : B) (t : B -> Prop) (h1 : @IN B b t) : term81 B b t e'.
Proof. exact (@lem5073423 B (term61 B t) e' b t h1). Qed.
Lemma lem5073432 {B : Type'} (e' : nat) (b : B) (t : B -> Prop) (h1 : @IN B b t) : term82 B b t e'.
Proof. exact (@lem5073431 B e' b t h1 (@lem5073430 B t)). Qed.
Lemma lem5073436 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (eq_refl (@CARD B t)). Qed.
Lemma lem5073437 {B : Type'} (t : B -> Prop) : term83 B t.
Proof. exact (fun h0 : ~ True => @lem5073436 B t). Qed.
Lemma lem5073438 {B : Type'} (b : B) (t : B -> Prop) (h1 : @IN B b t) : term84 B b t.
Proof. exact (@lem5073432 B (@CARD B t) b t h1). Qed.
Lemma lem5073439 {B : Type'} (b : B) (t : B -> Prop) (h1 : @IN B b t) : (term33 B b t) = (term77 B t).
Proof. exact (@lem5073438 B b t h1 (@lem5073437 B t)). Qed.
Lemma lem5073441 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5073442 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem5073441 nat t2 t1). Qed.
Lemma lem5073443 {B : Type'} (t : B -> Prop) : (term77 B t) = (term61 B t).
Proof. exact (@lem5073442 (@CARD B t) (term61 B t)). Qed.
Lemma lem5073444 {B : Type'} (b : B) (t : B -> Prop) (h1 : @IN B b t) : (term33 B b t) = (term61 B t).
Proof. exact (TRANS (@lem5073439 B b t h1) (@lem5073443 B t)). Qed.
Lemma lem5073445 {B : Type'} (b : B) (t : B -> Prop) (h1 : @FINITE B t) (h2 : @IN B b t) : (term32 B t b) = (term61 B t).
Proof. exact (TRANS (@lem5073403 B b t h1) (@lem5073444 B b t h2)). Qed.
Lemma lem5073446 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : ((term32 A s a) = (term32 B t b)) = ((term61 B t) = (term61 B t)).
Proof. exact (MK_COMB (@lem5073394 A B t a s h1 h3 h4) (@lem5073445 B b t h2 h5)). Qed.
Lemma lem5073448 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5073449 (x : nat) : (x = x) = True.
Proof. exact (@lem5073448 nat x). Qed.
Lemma lem5073450 {B : Type'} (t : B -> Prop) : ((term61 B t) = (term61 B t)) = True.
Proof. exact (@lem5073449 (term61 B t)). Qed.
Lemma lem5073451 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : ((term32 A s a) = (term32 B t b)) = True.
Proof. exact (TRANS (@lem5073446 A B a s b t h1 h2 h3 h4 h5) (@lem5073450 B t)). Qed.
Lemma lem5073452 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term85 A B s a t b) = (True /\ True).
Proof. exact (MK_COMB (@lem5073333 B b t h2) (@lem5073451 A B a s b t h1 h2 h3 h4 h5)). Qed.
Lemma lem5073454 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5073455 : (True /\ True) = True.
Proof. exact (@lem5073454 True). Qed.
Lemma lem5073456 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term85 A B s a t b) = True.
Proof. exact (TRANS (@lem5073452 A B a s b t h1 h2 h3 h4 h5) (@lem5073455)). Qed.
Lemma lem5073457 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term48 A B s a t b) = (True /\ True).
Proof. exact (MK_COMB (@lem5073322 A a s h1) (@lem5073456 A B a s b t h1 h2 h3 h4 h5)). Qed.
Lemma lem5073459 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5073460 : (True /\ True) = True.
Proof. exact (@lem5073459 True). Qed.
Lemma lem5073461 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term48 A B s a t b) = True.
Proof. exact (TRANS (@lem5073457 A B a s b t h1 h2 h3 h4 h5) (@lem5073460)). Qed.
Lemma lem5073462 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (q' : Prop) : term86 A B t b s a q'.
Proof. exact (@lem5073311 A B t b s a True q'). Qed.
Lemma lem5073463 {A B : Type'} (q' : Prop) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term87 A B t b s a q'.
Proof. exact (@lem5073462 A B t b s a q' (@lem5073461 A B a s b t h1 h2 h3 h4 h5)). Qed.
Lemma lem5073486 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term38 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5073487 (p : Prop) (q : Prop) (p' : Prop) : term39 p q p'.
Proof. exact (fun q' : Prop => @lem5073486 p q p' q'). Qed.
Lemma lem5073488 (p : Prop) (q : Prop) : term40 p q.
Proof. exact (fun p' : Prop => @lem5073487 p q p'). Qed.
Lemma lem5073489 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : term88 A B s a t b g f x.
Proof. exact (@lem5073488 (term26 A x s a) (term89 A B t b g f x)). Qed.
Lemma lem5073490 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (p' : Prop) : term90 A B s a t b g f x p'.
Proof. exact (@lem5073489 A B s a t b g f x p'). Qed.
Lemma lem5073491 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (p' : Prop) : (term90 A B s a t b g f x p') = (term91 A B s a t b g f x p').
Proof. exact (eq_refl (term90 A B s a t b g f x p')). Qed.
Lemma lem5073492 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (p' : Prop) : term91 A B s a t b g f x p'.
Proof. exact (EQ_MP (@lem5073491 A B s a t b g f x p') (@lem5073490 A B s a t b g f x p')). Qed.
Lemma lem5073493 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term92 A B s a t b g f x p' q'.
Proof. exact (@lem5073492 A B s a t b g f x p' q'). Qed.
Lemma lem5073494 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term92 A B s a t b g f x p' q') = (term93 A B s a t b g f x p' q').
Proof. exact (eq_refl (term92 A B s a t b g f x p' q')). Qed.
Lemma lem5073495 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term93 A B s a t b g f x p' q'.
Proof. exact (EQ_MP (@lem5073494 A B s a t b g f x p' q') (@lem5073493 A B s a t b g f x p' q')). Qed.
Lemma lem5073497 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem5073257 A s x y) (@lem5073256 A s x y)). Qed.
Lemma lem5073498 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem5073497 A s x y). Qed.
Lemma lem5073499 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term26 A x s a) = (term27 A s x a).
Proof. exact (@lem5073498 A s x a). Qed.
Lemma lem5073504 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) (a : A) (q' : Prop) : term94 A B t b g f s x a q'.
Proof. exact (@lem5073495 A B s a t b g f x (term27 A s x a) q'). Qed.
Lemma lem5073505 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (s : A -> Prop) (x : A) (a : A) (q' : Prop) : term95 A B t b g f s x a q'.
Proof. exact (@lem5073504 A B t b g f s x a q' (@lem5073499 A s x a)). Qed.
Lemma lem5073527 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem5073257 A s x y) (@lem5073256 A s x y)). Qed.
Lemma lem5073528 {B : Type'} (s : B -> Prop) (x : B) (y : B) : (term26 B x s y) = (term27 B s x y).
Proof. exact (@lem5073527 B s x y). Qed.
Lemma lem5073529 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (b : B) : (term96 A B f x t b) = (term97 A B t f x b).
Proof. exact (@lem5073528 B t (f x) b). Qed.
Lemma lem5073534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5073535 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (b : B) : (term98 A B f x t b) = (term99 A B t f x b).
Proof. exact (MK_COMB (@lem5073534) (@lem5073529 A B t f x b)). Qed.
Lemma lem5073542 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term100 A B g f x) = x) = ((term100 A B g f x) = x).
Proof. exact (eq_refl ((term100 A B g f x) = x)). Qed.
Lemma lem5073543 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term89 A B t b g f x) = (term101 A B t b g f x).
Proof. exact (MK_COMB (@lem5073535 A B t f x b) (@lem5073542 A B g f x)). Qed.
Lemma lem5073552 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : term102 A B s a t b g f x.
Proof. exact (fun h0 : term27 A s x a => @lem5073543 A B t b g f x). Qed.
Lemma lem5073553 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : term103 A B s a t b g f x.
Proof. exact (@lem5073505 A B t b g f s x a (term101 A B t b g f x)). Qed.
Lemma lem5073554 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term104 A B s a t b g f x) = (term105 A B s a t b g f x).
Proof. exact (@lem5073553 A B s a t b g f x (@lem5073552 A B s a t b g f x)). Qed.
Lemma lem5073617 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term106 A B s a t b g f) = (term107 A B s a t b g f).
Proof. exact (fun_ext (fun x : A => @lem5073554 A B s a t b g f x)). Qed.
Lemma lem5073680 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5073681 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term108 A B s a t b g f) = (term109 A B s a t b g f).
Proof. exact (MK_COMB (@lem5073680 A) (@lem5073617 A B s a t b g f)). Qed.
Lemma lem5073748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5073749 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term110 A B s a t b g f) = (term111 A B s a t b g f).
Proof. exact (MK_COMB (@lem5073748) (@lem5073681 A B s a t b g f)). Qed.
Lemma lem5073823 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term38 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5073824 (p : Prop) (q : Prop) (p' : Prop) : term39 p q p'.
Proof. exact (fun q' : Prop => @lem5073823 p q p' q'). Qed.
Lemma lem5073825 (p : Prop) (q : Prop) : term40 p q.
Proof. exact (fun p' : Prop => @lem5073824 p q p'). Qed.
Lemma lem5073826 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : term112 A B t b s a f g y.
Proof. exact (@lem5073825 (term26 B y t b) (term113 A B s a f g y)). Qed.
Lemma lem5073827 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (p' : Prop) : term114 A B t b s a f g y p'.
Proof. exact (@lem5073826 A B t b s a f g y p'). Qed.
Lemma lem5073828 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (p' : Prop) : (term114 A B t b s a f g y p') = (term115 A B t b s a f g y p').
Proof. exact (eq_refl (term114 A B t b s a f g y p')). Qed.
Lemma lem5073829 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (p' : Prop) : term115 A B t b s a f g y p'.
Proof. exact (EQ_MP (@lem5073828 A B t b s a f g y p') (@lem5073827 A B t b s a f g y p')). Qed.
Lemma lem5073830 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (p' : Prop) (q' : Prop) : term116 A B t b s a f g y p' q'.
Proof. exact (@lem5073829 A B t b s a f g y p' q'). Qed.
Lemma lem5073831 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (p' : Prop) (q' : Prop) : (term116 A B t b s a f g y p' q') = (term117 A B t b s a f g y p' q').
Proof. exact (eq_refl (term116 A B t b s a f g y p' q')). Qed.
Lemma lem5073832 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (p' : Prop) (q' : Prop) : term117 A B t b s a f g y p' q'.
Proof. exact (EQ_MP (@lem5073831 A B t b s a f g y p' q') (@lem5073830 A B t b s a f g y p' q')). Qed.
Lemma lem5073834 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem5073257 A s x y) (@lem5073256 A s x y)). Qed.
Lemma lem5073835 {B : Type'} (s : B -> Prop) (x : B) (y : B) : (term26 B x s y) = (term27 B s x y).
Proof. exact (@lem5073834 B s x y). Qed.
Lemma lem5073836 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term26 B y t b) = (term27 B t y b).
Proof. exact (@lem5073835 B t y b). Qed.
Lemma lem5073841 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (y : B) (b : B) (q' : Prop) : term118 A B s a f g t y b q'.
Proof. exact (@lem5073832 A B t b s a f g y (term27 B t y b) q'). Qed.
Lemma lem5073842 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (y : B) (b : B) (q' : Prop) : term119 A B s a f g t y b q'.
Proof. exact (@lem5073841 A B s a f g t y b q' (@lem5073836 B t y b)). Qed.
Lemma lem5073864 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (EQ_MP (@lem5073257 A s x y) (@lem5073256 A s x y)). Qed.
Lemma lem5073865 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term26 A x s y) = (term27 A s x y).
Proof. exact (@lem5073864 A s x y). Qed.
Lemma lem5073866 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) (a : A) : (term120 A B g y s a) = (term121 A B s g y a).
Proof. exact (@lem5073865 A s (g y) a). Qed.
Lemma lem5073871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5073872 {A B : Type'} (s : A -> Prop) (g : B -> A) (y : B) (a : A) : (term122 A B g y s a) = (term123 A B s g y a).
Proof. exact (MK_COMB (@lem5073871) (@lem5073866 A B s g y a)). Qed.
Lemma lem5073879 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : ((term124 A B f g y) = y) = ((term124 A B f g y) = y).
Proof. exact (eq_refl ((term124 A B f g y) = y)). Qed.
Lemma lem5073880 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term113 A B s a f g y) = (term125 A B s a f g y).
Proof. exact (MK_COMB (@lem5073872 A B s g y a) (@lem5073879 A B f g y)). Qed.
Lemma lem5073889 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : term126 A B t b s a f g y.
Proof. exact (fun h0 : term27 B t y b => @lem5073880 A B s a f g y). Qed.
Lemma lem5073890 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : term127 A B t b s a f g y.
Proof. exact (@lem5073842 A B s a f g t y b (term125 A B s a f g y)). Qed.
Lemma lem5073891 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term128 A B t b s a f g y) = (term129 A B t b s a f g y).
Proof. exact (@lem5073890 A B t b s a f g y (@lem5073889 A B t b s a f g y)). Qed.
Lemma lem5073954 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term130 A B t b s a f g) = (term131 A B t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5073891 A B t b s a f g y)). Qed.
Lemma lem5074017 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5074018 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term132 A B t b s a f g) = (term133 A B t b s a f g).
Proof. exact (MK_COMB (@lem5074017 B) (@lem5073954 A B t b s a f g)). Qed.
Lemma lem5074085 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term134 A B t b s a f g) = (term135 A B t b s a f g).
Proof. exact (MK_COMB (@lem5073749 A B s a t b g f) (@lem5074018 A B t b s a f g)). Qed.
Lemma lem5074220 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term136 A B t b s a f) = (term137 A B t b s a f).
Proof. exact (fun_ext (fun g : B -> A => @lem5074085 A B t b s a f g)). Qed.
Lemma lem5074355 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5074356 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term138 A B t b s a f) = (term139 A B t b s a f).
Proof. exact (MK_COMB (@lem5074355 A B) (@lem5074220 A B t b s a f)). Qed.
Lemma lem5074495 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : (term140 A B t b s a) = (term141 A B t b s a).
Proof. exact (fun_ext (fun f : A -> B => @lem5074356 A B t b s a f)). Qed.
Lemma lem5074634 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5074635 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : (term49 A B t b s a) = (term142 A B t b s a).
Proof. exact (MK_COMB (@lem5074634 A B) (@lem5074495 A B t b s a)). Qed.
Lemma lem5074778 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : term143 A B t b s a.
Proof. exact (fun h0 : True => @lem5074635 A B t b s a). Qed.
Lemma lem5074779 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term144 A B t b s a.
Proof. exact (@lem5073463 A B (term142 A B t b s a) a s b t h1 h2 h3 h4 h5). Qed.
Lemma lem5074780 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term11 A B t b s a) = (term145 A B t b s a).
Proof. exact (@lem5074779 A B a s b t h1 h2 h3 h4 h5 (@lem5074778 A B t b s a)). Qed.
Lemma lem5074782 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5074783 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : (term145 A B t b s a) = (term142 A B t b s a).
Proof. exact (@lem5074782 (term142 A B t b s a)). Qed.
Lemma lem5074926 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term11 A B t b s a) = (term142 A B t b s a).
Proof. exact (TRANS (@lem5074780 A B a s b t h1 h2 h3 h4 h5) (@lem5074783 A B t b s a)). Qed.
Lemma lem5074927 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (q' : Prop) : term146 A B t b s a q'.
Proof. exact (@lem5073298 A B b a t s (term142 A B t b s a) q'). Qed.
Lemma lem5074928 {A B : Type'} (q' : Prop) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term147 A B t b s a q'.
Proof. exact (@lem5074927 A B t b s a q' (@lem5074926 A B a s b t h1 h2 h3 h4 h5)). Qed.
Lemma lem5075020 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term42 A B b a t s) = (term42 A B b a t s).
Proof. exact (eq_refl (term42 A B b a t s)). Qed.
Lemma lem5075021 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : term148 A B b a t s.
Proof. exact (fun h0 : term142 A B t b s a => @lem5075020 A B b a t s). Qed.
Lemma lem5075022 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term149 A B b a t s.
Proof. exact (@lem5074928 A B (term42 A B b a t s) a s b t h1 h2 h3 h4 h5). Qed.
Lemma lem5075023 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term150 A B b a t s) = (term151 A B b a t s).
Proof. exact (@lem5075022 A B a s b t h1 h2 h3 h4 h5 (@lem5075021 A B b a t s)). Qed.
Lemma lem5075025 {A : Type'} (P : A -> Prop) (Q : Prop) : (term19 A P Q) = (term20 A P Q).
Proof. exact (EQ_MP (@lem5073248 A P Q) (@lem5073247 A P Q)). Qed.
Lemma lem5075026 {A B : Type'} (P : type572 A B) (Q : Prop) : (term152 A B P Q) = (term153 A B P Q).
Proof. exact (@lem5075025 (A -> B) P Q). Qed.
Lemma lem5075027 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term154 A B b a t s) = (term155 A B b a t s).
Proof. exact (@lem5075026 A B (term141 A B t b s a) (term42 A B b a t s)). Qed.
Lemma lem5075028 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term156 A B t b s a f) = (term139 A B t b s a f).
Proof. exact (eq_refl (term156 A B t b s a f)). Qed.
Lemma lem5075029 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : (term157 A B t b s a) = (term141 A B t b s a).
Proof. exact (fun_ext (fun f : A -> B => @lem5075028 A B t b s a f)). Qed.
Lemma lem5075030 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5075031 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : (term158 A B t b s a) = (term142 A B t b s a).
Proof. exact (MK_COMB (@lem5075030 A B) (@lem5075029 A B t b s a)). Qed.
Lemma lem5075032 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5075033 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) : (term159 A B t b s a) = (term160 A B t b s a).
Proof. exact (MK_COMB (@lem5075032) (@lem5075031 A B t b s a)). Qed.
Lemma lem5075034 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term42 A B b a t s) = (term42 A B b a t s).
Proof. exact (eq_refl (term42 A B b a t s)). Qed.
Lemma lem5075035 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term154 A B b a t s) = (term151 A B b a t s).
Proof. exact (MK_COMB (@lem5075033 A B t b s a) (@lem5075034 A B b a t s)). Qed.
Lemma lem5075036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5075037 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term161 A B b a t s) = (term162 A B b a t s).
Proof. exact (MK_COMB (@lem5075036) (@lem5075035 A B b a t s)). Qed.
Lemma lem5075038 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term156 A B t b s a f) = (term139 A B t b s a f).
Proof. exact (eq_refl (term156 A B t b s a f)). Qed.
Lemma lem5075039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5075040 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term163 A B t b s a f) = (term164 A B t b s a f).
Proof. exact (MK_COMB (@lem5075039) (@lem5075038 A B t b s a f)). Qed.
Lemma lem5075041 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term42 A B b a t s) = (term42 A B b a t s).
Proof. exact (eq_refl (term42 A B b a t s)). Qed.
Lemma lem5075042 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term165 A B f b a t s) = (term166 A B f b a t s).
Proof. exact (MK_COMB (@lem5075040 A B t b s a f) (@lem5075041 A B b a t s)). Qed.
Lemma lem5075043 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term167 A B b a t s) = (term168 A B b a t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5075042 A B f b a t s)). Qed.
Lemma lem5075044 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5075045 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term155 A B b a t s) = (term169 A B b a t s).
Proof. exact (MK_COMB (@lem5075044 A B) (@lem5075043 A B b a t s)). Qed.
Lemma lem5075046 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : ((term154 A B b a t s) = (term155 A B b a t s)) = ((term151 A B b a t s) = (term169 A B b a t s)).
Proof. exact (MK_COMB (@lem5075037 A B b a t s) (@lem5075045 A B b a t s)). Qed.
Lemma lem5075047 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term151 A B b a t s) = (term169 A B b a t s).
Proof. exact (EQ_MP (@lem5075046 A B b a t s) (@lem5075027 A B b a t s)). Qed.
Lemma lem5075053 {A : Type'} (P : A -> Prop) (Q : Prop) : (term19 A P Q) = (term20 A P Q).
Proof. exact (EQ_MP (@lem5073248 A P Q) (@lem5073247 A P Q)). Qed.
Lemma lem5075054 {A B : Type'} (P : type805 A B) (Q : Prop) : (term170 A B P Q) = (term171 A B P Q).
Proof. exact (@lem5075053 (B -> A) P Q). Qed.
Lemma lem5075055 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term172 A B f b a t s) = (term173 A B f b a t s).
Proof. exact (@lem5075054 A B (term137 A B t b s a f) (term42 A B b a t s)). Qed.
Lemma lem5075056 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term174 A B t b s a f g) = (term135 A B t b s a f g).
Proof. exact (eq_refl (term174 A B t b s a f g)). Qed.
Lemma lem5075057 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term175 A B t b s a f) = (term137 A B t b s a f).
Proof. exact (fun_ext (fun g : B -> A => @lem5075056 A B t b s a f g)). Qed.
Lemma lem5075058 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5075059 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term176 A B t b s a f) = (term139 A B t b s a f).
Proof. exact (MK_COMB (@lem5075058 A B) (@lem5075057 A B t b s a f)). Qed.
Lemma lem5075060 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5075061 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) : (term177 A B t b s a f) = (term164 A B t b s a f).
Proof. exact (MK_COMB (@lem5075060) (@lem5075059 A B t b s a f)). Qed.
Lemma lem5075062 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term42 A B b a t s) = (term42 A B b a t s).
Proof. exact (eq_refl (term42 A B b a t s)). Qed.
Lemma lem5075063 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term172 A B f b a t s) = (term166 A B f b a t s).
Proof. exact (MK_COMB (@lem5075061 A B t b s a f) (@lem5075062 A B b a t s)). Qed.
Lemma lem5075064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5075065 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term178 A B f b a t s) = (term179 A B f b a t s).
Proof. exact (MK_COMB (@lem5075064) (@lem5075063 A B f b a t s)). Qed.
Lemma lem5075066 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term174 A B t b s a f g) = (term135 A B t b s a f g).
Proof. exact (eq_refl (term174 A B t b s a f g)). Qed.
Lemma lem5075067 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5075068 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term180 A B t b s a f g) = (term181 A B t b s a f g).
Proof. exact (MK_COMB (@lem5075067) (@lem5075066 A B t b s a f g)). Qed.
Lemma lem5075069 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term42 A B b a t s) = (term42 A B b a t s).
Proof. exact (eq_refl (term42 A B b a t s)). Qed.
Lemma lem5075070 {A B : Type'} (f : A -> B) (g : B -> A) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term182 A B f g b a t s) = (term183 A B f g b a t s).
Proof. exact (MK_COMB (@lem5075068 A B t b s a f g) (@lem5075069 A B b a t s)). Qed.
Lemma lem5075071 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term184 A B f b a t s) = (term185 A B f b a t s).
Proof. exact (fun_ext (fun g : B -> A => @lem5075070 A B f g b a t s)). Qed.
Lemma lem5075072 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5075073 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term173 A B f b a t s) = (term186 A B f b a t s).
Proof. exact (MK_COMB (@lem5075072 A B) (@lem5075071 A B f b a t s)). Qed.
Lemma lem5075074 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : ((term172 A B f b a t s) = (term173 A B f b a t s)) = ((term166 A B f b a t s) = (term186 A B f b a t s)).
Proof. exact (MK_COMB (@lem5075065 A B f b a t s) (@lem5075073 A B f b a t s)). Qed.
Lemma lem5075075 {A B : Type'} (f : A -> B) (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term166 A B f b a t s) = (term186 A B f b a t s).
Proof. exact (EQ_MP (@lem5075074 A B f b a t s) (@lem5075055 A B f b a t s)). Qed.
Lemma lem5075801 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term168 A B b a t s) = (term187 A B b a t s).
Proof. exact (fun_ext (fun f : A -> B => @lem5075075 A B f b a t s)). Qed.
Lemma lem5076527 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5076528 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term169 A B b a t s) = (term188 A B b a t s).
Proof. exact (MK_COMB (@lem5076527 A B) (@lem5075801 A B b a t s)). Qed.
Lemma lem5077258 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : (term151 A B b a t s) = (term188 A B b a t s).
Proof. exact (TRANS (@lem5075047 A B b a t s) (@lem5076528 A B b a t s)). Qed.
Lemma lem5077259 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term150 A B b a t s) = (term188 A B b a t s).
Proof. exact (TRANS (@lem5075023 A B a s b t h1 h2 h3 h4 h5) (@lem5077258 A B b a t s)). Qed.
Lemma lem5077260 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (term188 A B b a t s) = (term150 A B b a t s).
Proof. exact (SYM (@lem5077259 A B a s b t h1 h2 h3 h4 h5)). Qed.
Lemma lem5077261 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term135 A B t b s a f g) : term135 A B t b s a f g.
Proof. exact (h1). Qed.
Lemma lem5077262 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term133 A B t b s a f g) : term133 A B t b s a f g.
Proof. exact (h1). Qed.
Lemma lem5077263 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (h1 : term109 A B s a t b g f) : term109 A B s a t b g f.
Proof. exact (h1). Qed.
Lemma lem5077265 (p : Prop) : p = (term189 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5077266 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term190 A B t s f b a g) = (term191 A B t s f b a g).
Proof. exact (@lem5077265 (term190 A B t s f b a g)). Qed.
Lemma lem5077267 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term191 A B t s f b a g) = (term190 A B t s f b a g).
Proof. exact (SYM (@lem5077266 A B t s f b a g)). Qed.
Lemma lem5077268 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term192 A B t s f b a g) : term192 A B t s f b a g.
Proof. exact (h1). Qed.
Lemma lem5077271 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term193 A B t s f b a g) : term193 A B t s f b a g.
Proof. exact (h1). Qed.
Lemma lem5077272 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : term194 A B t s f b a g.
Proof. exact (fun h0 : term193 A B t s f b a g => @lem5077271 A B t s f b a g h0). Qed.
Lemma lem5077273 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term194 A B t s f b a g) : term194 A B t s f b a g.
Proof. exact (h1). Qed.
Lemma lem5077274 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term193 A B t s f b a g) : term193 A B t s f b a g.
Proof. exact (h1). Qed.
Lemma lem5077275 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term193 A B t s f b a g) (h2 : term194 A B t s f b a g) : term193 A B t s f b a g.
Proof. exact (@lem5077273 A B t s f b a g h2 (@lem5077274 A B t s f b a g h1)). Qed.
Lemma lem5077276 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term193 A B t s f b a g) : term195 A B t s f b a g.
Proof. exact (fun h0 : term194 A B t s f b a g => @lem5077275 A B t s f b a g h1 h0). Qed.
Lemma lem5077277 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term194 A B t s f b a g) : term194 A B t s f b a g.
Proof. exact (h1). Qed.
Lemma lem5077278 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term193 A B t s f b a g) (h2 : term194 A B t s f b a g) : term193 A B t s f b a g.
Proof. exact (@lem5077276 A B t s f b a g h1 (@lem5077277 A B t s f b a g h2)). Qed.
Lemma lem5077279 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (h1 : term194 A B t s f b a g) : term194 A B t s f b a g.
Proof. exact (fun h0 : term193 A B t s f b a g => @lem5077278 A B t s f b a g h0 h1). Qed.
Lemma lem5077280 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : term196 A B t s f b a g.
Proof. exact (fun h0 : term194 A B t s f b a g => @lem5077279 A B t s f b a g h0). Qed.
Lemma lem5077283 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : term194 A B t s f b a g.
Proof. exact (@lem5077280 A B t s f b a g (@lem5077272 A B t s f b a g)). Qed.
Lemma lem5077284 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : term194 A B t s f b a g.
Proof. exact (@lem5077283 A B t s f b a g). Qed.
Lemma lem5077348 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5077349 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term191 A B t s f b a g) = (term197 A B t s f b a g).
Proof. exact (@lem5077348 (term192 A B t s f b a g)). Qed.
Lemma lem5077351 (t : Prop) : (term198 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5077352 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term197 A B t s f b a g) = (term190 A B t s f b a g).
Proof. exact (@lem5077351 (term190 A B t s f b a g)). Qed.
Lemma lem5077355 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term191 A B t s f b a g) = (term190 A B t s f b a g).
Proof. exact (TRANS (@lem5077349 A B t s f b a g) (@lem5077352 A B t s f b a g)). Qed.
Lemma lem5077376 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term199 A B t b s a f g) = (term199 A B t b s a f g).
Proof. exact (eq_refl (term199 A B t b s a f g)). Qed.
Lemma lem5077377 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term200 A B t s f b a g) = (term201 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077376 A B t b s a f g) (@lem5077355 A B t s f b a g)). Qed.
Lemma lem5077380 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term202 A B s a t b g f) = (term202 A B s a t b g f).
Proof. exact (eq_refl (term202 A B s a t b g f)). Qed.
Lemma lem5077381 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term203 A B t s f b a g) = (term204 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077380 A B s a t b g f) (@lem5077377 A B t s f b a g)). Qed.
Lemma lem5077384 {B : Type'} (b : B) (t : B -> Prop) : (term205 B b t) = (term205 B b t).
Proof. exact (eq_refl (term205 B b t)). Qed.
Lemma lem5077385 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term206 A B t s f b a g) = (term207 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077384 B b t) (@lem5077381 A B t s f b a g)). Qed.
Lemma lem5077388 {A : Type'} (a : A) (s : A -> Prop) : (term205 A a s) = (term205 A a s).
Proof. exact (eq_refl (term205 A a s)). Qed.
Lemma lem5077389 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term208 A B t s f b a g) = (term209 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077388 A a s) (@lem5077385 A B t s f b a g)). Qed.
Lemma lem5077392 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term210 A B s t) = (term210 A B s t).
Proof. exact (eq_refl (term210 A B s t)). Qed.
Lemma lem5077393 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term211 A B t s f b a g) = (term212 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077392 A B s t) (@lem5077389 A B t s f b a g)). Qed.
Lemma lem5077396 {B : Type'} (t : B -> Prop) : (term213 B t) = (term213 B t).
Proof. exact (eq_refl (term213 B t)). Qed.
Lemma lem5077397 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term214 A B t s f b a g) = (term215 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077396 B t) (@lem5077393 A B t s f b a g)). Qed.
Lemma lem5077400 {A : Type'} (s : A -> Prop) : (term213 A s) = (term213 A s).
Proof. exact (eq_refl (term213 A s)). Qed.
Lemma lem5077401 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term193 A B t s f b a g) = (term216 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077400 A s) (@lem5077397 A B t s f b a g)). Qed.
Lemma lem5077404 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term217 A B s f b a g) = (term218 A B s f b a g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5077401 A B t s f b a g)). Qed.
Lemma lem5077405 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5077406 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term219 A B s f b a g) = (term220 A B s f b a g).
Proof. exact (MK_COMB (@lem5077405 B) (@lem5077404 A B s f b a g)). Qed.
Lemma lem5077411 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) : (term221 A B f b a g) = (term222 A B f b a g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5077406 A B s f b a g)). Qed.
Lemma lem5077412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5077413 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) : (term223 A B f b a g) = (term224 A B f b a g).
Proof. exact (MK_COMB (@lem5077412 A) (@lem5077411 A B f b a g)). Qed.
Lemma lem5077418 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term225 A B b a g) = (term226 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5077413 A B f b a g)). Qed.
Lemma lem5077419 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5077420 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term227 A B b a g) = (term228 A B b a g).
Proof. exact (MK_COMB (@lem5077419 A B) (@lem5077418 A B b a g)). Qed.
Lemma lem5077425 {A B : Type'} (a : A) (g : B -> A) : (term229 A B a g) = (term230 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5077420 A B b a g)). Qed.
Lemma lem5077426 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5077427 {A B : Type'} (a : A) (g : B -> A) : (term231 A B a g) = (term232 A B a g).
Proof. exact (MK_COMB (@lem5077426 B) (@lem5077425 A B a g)). Qed.
Lemma lem5077432 {A B : Type'} (g : B -> A) : (term233 A B g) = (term234 A B g).
Proof. exact (fun_ext (fun a : A => @lem5077427 A B a g)). Qed.
Lemma lem5077433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5077434 {A B : Type'} (g : B -> A) : (term235 A B g) = (term236 A B g).
Proof. exact (MK_COMB (@lem5077433 A) (@lem5077432 A B g)). Qed.
Lemma lem5077439 {A B : Type'} : (term237 A B) = (term238 A B).
Proof. exact (fun_ext (fun g : B -> A => @lem5077434 A B g)). Qed.
Lemma lem5077440 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5077441 {A B : Type'} : (term239 A B) = (term240 A B).
Proof. exact (MK_COMB (@lem5077440 A B) (@lem5077439 A B)). Qed.
Lemma lem5077446 {A B : Type'} (b : B) (f : A -> B) (a : A) : (term241 A B b f a) = (term242 A B b f a).
Proof. exact (eq_refl (term241 A B b f a)). Qed.
Lemma lem5077447 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5077448 {A B : Type'} (b : B) (f : A -> B) (a : A) : (term243 A B b f a) = (term244 A B b f a).
Proof. exact (MK_COMB (@lem5077447 B) (@lem5077446 A B b f a)). Qed.
Lemma lem5077449 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5077450 {A B : Type'} (f : A -> B) (a : A) (b : B) : ((term241 A B b f a) = b) = ((term242 A B b f a) = b).
Proof. exact (MK_COMB (@lem5077448 A B b f a) (@lem5077449 B b)). Qed.
Lemma lem5077451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077452 {A B : Type'} (f : A -> B) (a : A) (b : B) : (term245 A B f a b) = (term246 A B f a b).
Proof. exact (MK_COMB (@lem5077451) (@lem5077450 A B f a b)). Qed.
Lemma lem5077453 {A B : Type'} (a : A) (g : B -> A) (b : B) : (term247 A B a g b) = (term248 A B a g b).
Proof. exact (eq_refl (term247 A B a g b)). Qed.
Lemma lem5077454 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5077455 {A B : Type'} (a : A) (g : B -> A) (b : B) : (term249 A B a g b) = (term250 A B a g b).
Proof. exact (MK_COMB (@lem5077454 A) (@lem5077453 A B a g b)). Qed.
Lemma lem5077456 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5077457 {A B : Type'} (g : B -> A) (b : B) (a : A) : ((term247 A B a g b) = a) = ((term248 A B a g b) = a).
Proof. exact (MK_COMB (@lem5077455 A B a g b) (@lem5077456 A a)). Qed.
Lemma lem5077458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077459 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term251 A B g b a) = (term252 A B g b a).
Proof. exact (MK_COMB (@lem5077458) (@lem5077457 A B g b a)). Qed.
Lemma lem5077460 {A B : Type'} (a : A) (b : B) (f : A -> B) (x : A) : (term253 A B a b f x) = (term254 A B a b f x).
Proof. exact (eq_refl (term253 A B a b f x)). Qed.
Lemma lem5077461 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5077462 {A B : Type'} (a : A) (b : B) (f : A -> B) (x : A) : (term255 A B a b f x) = (term256 A B a b f x).
Proof. exact (MK_COMB (@lem5077461 B) (@lem5077460 A B a b f x)). Qed.
Lemma lem5077463 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5077464 {A B : Type'} (a : A) (b : B) (f : A -> B) (x : A) (t : B -> Prop) : (term257 A B a b f x t) = (term258 A B a b f x t).
Proof. exact (MK_COMB (@lem5077462 A B a b f x) (@lem5077463 B t)). Qed.
Lemma lem5077465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077466 {A B : Type'} (a : A) (b : B) (f : A -> B) (x : A) (t : B -> Prop) : (term259 A B a b f x t) = (term260 A B a b f x t).
Proof. exact (MK_COMB (@lem5077465) (@lem5077464 A B a b f x t)). Qed.
Lemma lem5077467 {A B : Type'} (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term261 A B g a b f x) = (term262 A B g a b f x).
Proof. exact (eq_refl (term261 A B g a b f x)). Qed.
Lemma lem5077468 {A B : Type'} (a : A) (b : B) (f : A -> B) (x : A) : (term253 A B a b f x) = (term254 A B a b f x).
Proof. exact (eq_refl (term253 A B a b f x)). Qed.
Lemma lem5077469 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5077470 {A B : Type'} (a : A) (b : B) (f : A -> B) (x : A) : (term263 A B a b f x) = (term264 A B a b f x).
Proof. exact (MK_COMB (@lem5077469 B) (@lem5077468 A B a b f x)). Qed.
Lemma lem5077471 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5077472 {A B : Type'} (a : A) (f : A -> B) (x : A) (b : B) : ((term253 A B a b f x) = b) = ((term254 A B a b f x) = b).
Proof. exact (MK_COMB (@lem5077470 A B a b f x) (@lem5077471 B b)). Qed.
Lemma lem5077473 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5077474 {A B : Type'} (a : A) (f : A -> B) (x : A) (b : B) : (term265 A B a f x b) = (term266 A B a f x b).
Proof. exact (MK_COMB (@lem5077473 A) (@lem5077472 A B a f x b)). Qed.
Lemma lem5077475 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5077476 {A B : Type'} (f : A -> B) (x : A) (b : B) (a : A) : (term267 A B f x b a) = (term268 A B f x b a).
Proof. exact (MK_COMB (@lem5077474 A B a f x b) (@lem5077475 A a)). Qed.
Lemma lem5077477 {A B : Type'} (a : A) (b : B) (f : A -> B) (x : A) : (term253 A B a b f x) = (term254 A B a b f x).
Proof. exact (eq_refl (term253 A B a b f x)). Qed.
Lemma lem5077478 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5077479 {A B : Type'} (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term269 A B g a b f x) = (term270 A B g a b f x).
Proof. exact (MK_COMB (@lem5077478 A B g) (@lem5077477 A B a b f x)). Qed.
Lemma lem5077480 {A B : Type'} (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term262 A B g a b f x) = (term271 A B g a b f x).
Proof. exact (MK_COMB (@lem5077476 A B f x b a) (@lem5077479 A B g a b f x)). Qed.
Lemma lem5077481 {A B : Type'} (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term261 A B g a b f x) = (term271 A B g a b f x).
Proof. exact (TRANS (@lem5077467 A B g a b f x) (@lem5077480 A B g a b f x)). Qed.
Lemma lem5077482 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5077483 {A B : Type'} (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term272 A B g a b f x) = (term273 A B g a b f x).
Proof. exact (MK_COMB (@lem5077482 A) (@lem5077481 A B g a b f x)). Qed.
Lemma lem5077484 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5077485 {A B : Type'} (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : ((term261 A B g a b f x) = x) = ((term271 A B g a b f x) = x).
Proof. exact (MK_COMB (@lem5077483 A B g a b f x) (@lem5077484 A x)). Qed.
Lemma lem5077486 {A B : Type'} (t : B -> Prop) (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term274 A B t g a b f x) = (term275 A B t g a b f x).
Proof. exact (MK_COMB (@lem5077466 A B a b f x t) (@lem5077485 A B g a b f x)). Qed.
Lemma lem5077487 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (term205 A x s).
Proof. exact (eq_refl (term205 A x s)). Qed.
Lemma lem5077488 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term276 A B s t g a b f x) = (term277 A B s t g a b f x).
Proof. exact (MK_COMB (@lem5077487 A x s) (@lem5077486 A B t g a b f x)). Qed.
Lemma lem5077489 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (a : A) (b : B) (f : A -> B) : (term278 A B s t g a b f) = (term279 A B s t g a b f).
Proof. exact (fun_ext (fun x : A => @lem5077488 A B s t g a b f x)). Qed.
Lemma lem5077490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5077491 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (a : A) (b : B) (f : A -> B) : (term280 A B s t g a b f) = (term281 A B s t g a b f).
Proof. exact (MK_COMB (@lem5077490 A) (@lem5077489 A B s t g a b f)). Qed.
Lemma lem5077492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077493 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (a : A) (b : B) (f : A -> B) : (term282 A B s t g a b f) = (term283 A B s t g a b f).
Proof. exact (MK_COMB (@lem5077492) (@lem5077491 A B s t g a b f)). Qed.
Lemma lem5077494 {A B : Type'} (b : B) (a : A) (g : B -> A) (y : B) : (term284 A B b a g y) = (term285 A B b a g y).
Proof. exact (eq_refl (term284 A B b a g y)). Qed.
Lemma lem5077495 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5077496 {A B : Type'} (b : B) (a : A) (g : B -> A) (y : B) : (term286 A B b a g y) = (term287 A B b a g y).
Proof. exact (MK_COMB (@lem5077495 A) (@lem5077494 A B b a g y)). Qed.
Lemma lem5077497 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5077498 {A B : Type'} (b : B) (a : A) (g : B -> A) (y : B) (s : A -> Prop) : (term288 A B b a g y s) = (term289 A B b a g y s).
Proof. exact (MK_COMB (@lem5077496 A B b a g y) (@lem5077497 A s)). Qed.
Lemma lem5077499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077500 {A B : Type'} (b : B) (a : A) (g : B -> A) (y : B) (s : A -> Prop) : (term290 A B b a g y s) = (term291 A B b a g y s).
Proof. exact (MK_COMB (@lem5077499) (@lem5077498 A B b a g y s)). Qed.
Lemma lem5077501 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term292 A B f b a g y) = (term293 A B f b a g y).
Proof. exact (eq_refl (term292 A B f b a g y)). Qed.
Lemma lem5077502 {A B : Type'} (b : B) (a : A) (g : B -> A) (y : B) : (term284 A B b a g y) = (term285 A B b a g y).
Proof. exact (eq_refl (term284 A B b a g y)). Qed.
Lemma lem5077503 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5077504 {A B : Type'} (b : B) (a : A) (g : B -> A) (y : B) : (term294 A B b a g y) = (term295 A B b a g y).
Proof. exact (MK_COMB (@lem5077503 A) (@lem5077502 A B b a g y)). Qed.
Lemma lem5077505 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5077506 {A B : Type'} (b : B) (g : B -> A) (y : B) (a : A) : ((term284 A B b a g y) = a) = ((term285 A B b a g y) = a).
Proof. exact (MK_COMB (@lem5077504 A B b a g y) (@lem5077505 A a)). Qed.
Lemma lem5077507 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5077508 {A B : Type'} (b : B) (g : B -> A) (y : B) (a : A) : (term296 A B b g y a) = (term297 A B b g y a).
Proof. exact (MK_COMB (@lem5077507 B) (@lem5077506 A B b g y a)). Qed.
Lemma lem5077509 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5077510 {A B : Type'} (g : B -> A) (y : B) (a : A) (b : B) : (term298 A B g y a b) = (term299 A B g y a b).
Proof. exact (MK_COMB (@lem5077508 A B b g y a) (@lem5077509 B b)). Qed.
Lemma lem5077511 {A B : Type'} (b : B) (a : A) (g : B -> A) (y : B) : (term284 A B b a g y) = (term285 A B b a g y).
Proof. exact (eq_refl (term284 A B b a g y)). Qed.
Lemma lem5077512 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5077513 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term300 A B f b a g y) = (term301 A B f b a g y).
Proof. exact (MK_COMB (@lem5077512 A B f) (@lem5077511 A B b a g y)). Qed.
Lemma lem5077514 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term293 A B f b a g y) = (term302 A B f b a g y).
Proof. exact (MK_COMB (@lem5077510 A B g y a b) (@lem5077513 A B f b a g y)). Qed.
Lemma lem5077515 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term292 A B f b a g y) = (term302 A B f b a g y).
Proof. exact (TRANS (@lem5077501 A B f b a g y) (@lem5077514 A B f b a g y)). Qed.
Lemma lem5077516 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5077517 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term303 A B f b a g y) = (term304 A B f b a g y).
Proof. exact (MK_COMB (@lem5077516 B) (@lem5077515 A B f b a g y)). Qed.
Lemma lem5077518 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5077519 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : ((term292 A B f b a g y) = y) = ((term302 A B f b a g y) = y).
Proof. exact (MK_COMB (@lem5077517 A B f b a g y) (@lem5077518 B y)). Qed.
Lemma lem5077520 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term305 A B s f b a g y) = (term306 A B s f b a g y).
Proof. exact (MK_COMB (@lem5077500 A B b a g y s) (@lem5077519 A B f b a g y)). Qed.
Lemma lem5077521 {B : Type'} (y : B) (t : B -> Prop) : (term205 B y t) = (term205 B y t).
Proof. exact (eq_refl (term205 B y t)). Qed.
Lemma lem5077522 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term307 A B t s f b a g y) = (term308 A B t s f b a g y).
Proof. exact (MK_COMB (@lem5077521 B y t) (@lem5077520 A B s f b a g y)). Qed.
Lemma lem5077523 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term309 A B t s f b a g) = (term310 A B t s f b a g).
Proof. exact (fun_ext (fun y : B => @lem5077522 A B t s f b a g y)). Qed.
Lemma lem5077524 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5077525 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term311 A B t s f b a g) = (term312 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077524 B) (@lem5077523 A B t s f b a g)). Qed.
Lemma lem5077526 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term313 A B t s f b a g) = (term314 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077493 A B s t g a b f) (@lem5077525 A B t s f b a g)). Qed.
Lemma lem5077527 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term315 A B t s f b a g) = (term316 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077459 A B g b a) (@lem5077526 A B t s f b a g)). Qed.
Lemma lem5077528 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term190 A B t s f b a g) = (term317 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077452 A B f a b) (@lem5077527 A B t s f b a g)). Qed.
Lemma lem5077529 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term199 A B t b s a f g) = (term199 A B t b s a f g).
Proof. exact (eq_refl (term199 A B t b s a f g)). Qed.
Lemma lem5077530 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term201 A B t s f b a g) = (term318 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077529 A B t b s a f g) (@lem5077528 A B t s f b a g)). Qed.
Lemma lem5077531 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term202 A B s a t b g f) = (term202 A B s a t b g f).
Proof. exact (eq_refl (term202 A B s a t b g f)). Qed.
Lemma lem5077532 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term204 A B t s f b a g) = (term319 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077531 A B s a t b g f) (@lem5077530 A B t s f b a g)). Qed.
Lemma lem5077533 {B : Type'} (b : B) (t : B -> Prop) : (term205 B b t) = (term205 B b t).
Proof. exact (eq_refl (term205 B b t)). Qed.
Lemma lem5077534 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term207 A B t s f b a g) = (term320 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077533 B b t) (@lem5077532 A B t s f b a g)). Qed.
Lemma lem5077535 {A : Type'} (a : A) (s : A -> Prop) : (term205 A a s) = (term205 A a s).
Proof. exact (eq_refl (term205 A a s)). Qed.
Lemma lem5077536 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term209 A B t s f b a g) = (term321 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077535 A a s) (@lem5077534 A B t s f b a g)). Qed.
Lemma lem5077537 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term210 A B s t) = (term210 A B s t).
Proof. exact (eq_refl (term210 A B s t)). Qed.
Lemma lem5077538 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term212 A B t s f b a g) = (term322 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077537 A B s t) (@lem5077536 A B t s f b a g)). Qed.
Lemma lem5077539 {B : Type'} (t : B -> Prop) : (term213 B t) = (term213 B t).
Proof. exact (eq_refl (term213 B t)). Qed.
Lemma lem5077540 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term215 A B t s f b a g) = (term323 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077539 B t) (@lem5077538 A B t s f b a g)). Qed.
Lemma lem5077541 {A : Type'} (s : A -> Prop) : (term213 A s) = (term213 A s).
Proof. exact (eq_refl (term213 A s)). Qed.
Lemma lem5077542 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term216 A B t s f b a g) = (term324 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077541 A s) (@lem5077540 A B t s f b a g)). Qed.
Lemma lem5077543 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term218 A B s f b a g) = (term325 A B s f b a g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5077542 A B t s f b a g)). Qed.
Lemma lem5077544 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5077545 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term220 A B s f b a g) = (term326 A B s f b a g).
Proof. exact (MK_COMB (@lem5077544 B) (@lem5077543 A B s f b a g)). Qed.
Lemma lem5077546 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) : (term222 A B f b a g) = (term327 A B f b a g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5077545 A B s f b a g)). Qed.
Lemma lem5077547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5077548 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) : (term224 A B f b a g) = (term328 A B f b a g).
Proof. exact (MK_COMB (@lem5077547 A) (@lem5077546 A B f b a g)). Qed.
Lemma lem5077549 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term226 A B b a g) = (term329 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5077548 A B f b a g)). Qed.
Lemma lem5077550 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5077551 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term228 A B b a g) = (term330 A B b a g).
Proof. exact (MK_COMB (@lem5077550 A B) (@lem5077549 A B b a g)). Qed.
Lemma lem5077552 {A B : Type'} (a : A) (g : B -> A) : (term230 A B a g) = (term331 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5077551 A B b a g)). Qed.
Lemma lem5077553 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5077554 {A B : Type'} (a : A) (g : B -> A) : (term232 A B a g) = (term332 A B a g).
Proof. exact (MK_COMB (@lem5077553 B) (@lem5077552 A B a g)). Qed.
Lemma lem5077555 {A B : Type'} (g : B -> A) : (term234 A B g) = (term333 A B g).
Proof. exact (fun_ext (fun a : A => @lem5077554 A B a g)). Qed.
Lemma lem5077556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5077557 {A B : Type'} (g : B -> A) : (term236 A B g) = (term334 A B g).
Proof. exact (MK_COMB (@lem5077556 A) (@lem5077555 A B g)). Qed.
Lemma lem5077558 {A B : Type'} : (term238 A B) = (term335 A B).
Proof. exact (fun_ext (fun g : B -> A => @lem5077557 A B g)). Qed.
Lemma lem5077559 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5077560 {A B : Type'} : (term240 A B) = (term336 A B).
Proof. exact (MK_COMB (@lem5077559 A B) (@lem5077558 A B)). Qed.
Lemma lem5077563 {A B : Type'} : (term239 A B) = (term336 A B).
Proof. exact (TRANS (@lem5077441 A B) (@lem5077560 A B)). Qed.
Lemma lem5077605 {A : Type'} (a : A) (h1 : (a = a) = False) : (a = a) = False.
Proof. exact (h1). Qed.
Lemma lem5077606 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5077607 {A B : Type'} (a : A) (h1 : (a = a) = False) : (term337 A B a) = (@COND B False).
Proof. exact (MK_COMB (@lem5077606 B) (@lem5077605 A a h1)). Qed.
Lemma lem5077608 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5077609 {A B : Type'} (b : B) (a : A) (h1 : (a = a) = False) : (term338 A B a b) = (@COND B False b).
Proof. exact (MK_COMB (@lem5077607 A B a h1) (@lem5077608 B b)). Qed.
Lemma lem5077610 {A B : Type'} (f : A -> B) (a : A) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem5077611 {A B : Type'} (b : B) (f : A -> B) (a : A) (h1 : (a = a) = False) : (term242 A B b f a) = (term339 A B b f a).
Proof. exact (MK_COMB (@lem5077609 A B b a h1) (@lem5077610 A B f a)). Qed.
Lemma lem5077613 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5077614 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5077613 B t1 t2). Qed.
Lemma lem5077615 {A B : Type'} (b : B) (f : A -> B) (a : A) : (term339 A B b f a) = (f a).
Proof. exact (@lem5077614 B b (f a)). Qed.
Lemma lem5077616 {A B : Type'} (b : B) (f : A -> B) (a : A) (h1 : (a = a) = False) : (term242 A B b f a) = (f a).
Proof. exact (TRANS (@lem5077611 A B b f a h1) (@lem5077615 A B b f a)). Qed.
Lemma lem5077617 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5077618 {A B : Type'} (b : B) (f : A -> B) (a : A) (h1 : (a = a) = False) : (term244 A B b f a) = (term340 A B f a).
Proof. exact (MK_COMB (@lem5077617 B) (@lem5077616 A B b f a h1)). Qed.
Lemma lem5077619 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5077620 {A B : Type'} (f : A -> B) (b : B) (a : A) (h1 : (a = a) = False) : ((term242 A B b f a) = b) = ((f a) = b).
Proof. exact (MK_COMB (@lem5077618 A B b f a h1) (@lem5077619 B b)). Qed.
Lemma lem5077623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077624 {A B : Type'} (f : A -> B) (b : B) (a : A) (h1 : (a = a) = False) : (term246 A B f a b) = (term341 A B f a b).
Proof. exact (MK_COMB (@lem5077623) (@lem5077620 A B f b a h1)). Qed.
Lemma lem5077626 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5077627 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5077626 B x). Qed.
Lemma lem5077628 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem5077627 B b). Qed.
Lemma lem5077629 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5077630 {A B : Type'} (b : B) : (term342 A B b) = (@COND A True).
Proof. exact (MK_COMB (@lem5077629 A) (@lem5077628 B b)). Qed.
Lemma lem5077631 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5077632 {A B : Type'} (b : B) (a : A) : (term343 A B b a) = (@COND A True a).
Proof. exact (MK_COMB (@lem5077630 A B b) (@lem5077631 A a)). Qed.
Lemma lem5077633 {A B : Type'} (g : B -> A) (b : B) : (g b) = (g b).
Proof. exact (eq_refl (g b)). Qed.
Lemma lem5077634 {A B : Type'} (a : A) (g : B -> A) (b : B) : (term248 A B a g b) = (term344 A B a g b).
Proof. exact (MK_COMB (@lem5077632 A B b a) (@lem5077633 A B g b)). Qed.
Lemma lem5077636 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5077637 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem5077636 A t2 t1). Qed.
Lemma lem5077638 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term344 A B a g b) = a.
Proof. exact (@lem5077637 A (g b) a). Qed.
Lemma lem5077639 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term248 A B a g b) = a.
Proof. exact (TRANS (@lem5077634 A B a g b) (@lem5077638 A B g b a)). Qed.
Lemma lem5077640 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5077641 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term250 A B a g b) = (@eq A a).
Proof. exact (MK_COMB (@lem5077640 A) (@lem5077639 A B g b a)). Qed.
Lemma lem5077642 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5077643 {A B : Type'} (g : B -> A) (b : B) (a : A) : ((term248 A B a g b) = a) = (a = a).
Proof. exact (MK_COMB (@lem5077641 A B g b a) (@lem5077642 A a)). Qed.
Lemma lem5077645 {A : Type'} (a : A) (h1 : (a = a) = False) : (a = a) = False.
Proof. exact (h1). Qed.
Lemma lem5077646 {A B : Type'} (g : B -> A) (b : B) (a : A) (h1 : (a = a) = False) : ((term248 A B a g b) = a) = False.
Proof. exact (TRANS (@lem5077643 A B g b a) (@lem5077645 A a h1)). Qed.
Lemma lem5077647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077648 {A B : Type'} (g : B -> A) (b : B) (a : A) (h1 : (a = a) = False) : (term252 A B g b a) = (and False).
Proof. exact (MK_COMB (@lem5077647) (@lem5077646 A B g b a h1)). Qed.
Lemma lem5077703 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term314 A B t s f b a g) = (term314 A B t s f b a g).
Proof. exact (eq_refl (term314 A B t s f b a g)). Qed.
Lemma lem5077704 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term316 A B t s f b a g) = (term345 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077648 A B g b a h1) (@lem5077703 A B t s f b a g)). Qed.
Lemma lem5077706 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5077707 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term345 A B t s f b a g) = False.
Proof. exact (@lem5077706 (term314 A B t s f b a g)). Qed.
Lemma lem5077708 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term316 A B t s f b a g) = False.
Proof. exact (TRANS (@lem5077704 A B t s f b g a h1) (@lem5077707 A B t s f b a g)). Qed.
Lemma lem5077709 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (b : B) (a : A) (h1 : (a = a) = False) : (term317 A B t s f b a g) = (term346 A B f a b).
Proof. exact (MK_COMB (@lem5077624 A B f b a h1) (@lem5077708 A B t s f b g a h1)). Qed.
Lemma lem5077711 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5077712 {A B : Type'} (f : A -> B) (a : A) (b : B) : (term346 A B f a b) = False.
Proof. exact (@lem5077711 ((f a) = b)). Qed.
Lemma lem5077713 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term317 A B t s f b a g) = False.
Proof. exact (TRANS (@lem5077709 A B t s g f b a h1) (@lem5077712 A B f a b)). Qed.
Lemma lem5077714 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term199 A B t b s a f g) = (term199 A B t b s a f g).
Proof. exact (eq_refl (term199 A B t b s a f g)). Qed.
Lemma lem5077715 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term318 A B t s f b a g) = (term347 A B t b s a f g).
Proof. exact (MK_COMB (@lem5077714 A B t b s a f g) (@lem5077713 A B t s f b g a h1)). Qed.
Lemma lem5077717 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5077718 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term347 A B t b s a f g) = (term348 A B t b s a f g).
Proof. exact (@lem5077717 (term133 A B t b s a f g)). Qed.
Lemma lem5077719 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term318 A B t s f b a g) = (term348 A B t b s a f g).
Proof. exact (TRANS (@lem5077715 A B t b s f g a h1) (@lem5077718 A B t b s a f g)). Qed.
Lemma lem5077720 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term202 A B s a t b g f) = (term202 A B s a t b g f).
Proof. exact (eq_refl (term202 A B s a t b g f)). Qed.
Lemma lem5077721 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term319 A B t s f b a g) = (term349 A B t b s a f g).
Proof. exact (MK_COMB (@lem5077720 A B s a t b g f) (@lem5077719 A B t b s f g a h1)). Qed.
Lemma lem5077724 {B : Type'} (b : B) (t : B -> Prop) : (term205 B b t) = (term205 B b t).
Proof. exact (eq_refl (term205 B b t)). Qed.
Lemma lem5077725 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term320 A B t s f b a g) = (term350 A B t b s a f g).
Proof. exact (MK_COMB (@lem5077724 B b t) (@lem5077721 A B t b s f g a h1)). Qed.
Lemma lem5077728 {A : Type'} (a : A) (s : A -> Prop) : (term205 A a s) = (term205 A a s).
Proof. exact (eq_refl (term205 A a s)). Qed.
Lemma lem5077729 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term321 A B t s f b a g) = (term351 A B t b s a f g).
Proof. exact (MK_COMB (@lem5077728 A a s) (@lem5077725 A B t b s f g a h1)). Qed.
Lemma lem5077732 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term210 A B s t) = (term210 A B s t).
Proof. exact (eq_refl (term210 A B s t)). Qed.
Lemma lem5077733 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term322 A B t s f b a g) = (term352 A B t b s a f g).
Proof. exact (MK_COMB (@lem5077732 A B s t) (@lem5077729 A B t b s f g a h1)). Qed.
Lemma lem5077738 {B : Type'} (t : B -> Prop) : (term213 B t) = (term213 B t).
Proof. exact (eq_refl (term213 B t)). Qed.
Lemma lem5077739 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term323 A B t s f b a g) = (term353 A B t b s a f g).
Proof. exact (MK_COMB (@lem5077738 B t) (@lem5077733 A B t b s f g a h1)). Qed.
Lemma lem5077742 {A : Type'} (s : A -> Prop) : (term213 A s) = (term213 A s).
Proof. exact (eq_refl (term213 A s)). Qed.
Lemma lem5077743 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term324 A B t s f b a g) = (term354 A B t b s a f g).
Proof. exact (MK_COMB (@lem5077742 A s) (@lem5077739 A B t b s f g a h1)). Qed.
Lemma lem5077746 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term325 A B s f b a g) = (term355 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5077743 A B t b s f g a h1)). Qed.
Lemma lem5077747 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5077748 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term326 A B s f b a g) = (term356 A B b s a f g).
Proof. exact (MK_COMB (@lem5077747 B) (@lem5077746 A B b s f g a h1)). Qed.
Lemma lem5077753 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term327 A B f b a g) = (term357 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5077748 A B b s f g a h1)). Qed.
Lemma lem5077754 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5077755 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term328 A B f b a g) = (term358 A B b a f g).
Proof. exact (MK_COMB (@lem5077754 A) (@lem5077753 A B b f g a h1)). Qed.
Lemma lem5077760 {A B : Type'} (b : B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term329 A B b a g) = (term359 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5077755 A B b f g a h1)). Qed.
Lemma lem5077761 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5077762 {A B : Type'} (b : B) (g : B -> A) (a : A) (h1 : (a = a) = False) : (term330 A B b a g) = (term360 A B b a g).
Proof. exact (MK_COMB (@lem5077761 A B) (@lem5077760 A B b g a h1)). Qed.
Lemma lem5077767 {A B : Type'} (g : B -> A) (a : A) (h1 : (a = a) = False) : (term331 A B a g) = (term361 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5077762 A B b g a h1)). Qed.
Lemma lem5077768 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5077769 {A B : Type'} (g : B -> A) (a : A) (h1 : (a = a) = False) : (term332 A B a g) = (term362 A B a g).
Proof. exact (MK_COMB (@lem5077768 B) (@lem5077767 A B g a h1)). Qed.
Lemma lem5077774 {A B : Type'} (a : A) (g : B -> A) : term363 A B a g.
Proof. exact (fun h0 : (a = a) = False => @lem5077769 A B g a h0). Qed.
Lemma lem5077814 {A : Type'} (a : A) (h1 : (a = a) = True) : (a = a) = True.
Proof. exact (h1). Qed.
Lemma lem5077815 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5077816 {A B : Type'} (a : A) (h1 : (a = a) = True) : (term337 A B a) = (@COND B True).
Proof. exact (MK_COMB (@lem5077815 B) (@lem5077814 A a h1)). Qed.
Lemma lem5077817 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5077818 {A B : Type'} (b : B) (a : A) (h1 : (a = a) = True) : (term338 A B a b) = (@COND B True b).
Proof. exact (MK_COMB (@lem5077816 A B a h1) (@lem5077817 B b)). Qed.
Lemma lem5077819 {A B : Type'} (f : A -> B) (a : A) : (f a) = (f a).
Proof. exact (eq_refl (f a)). Qed.
Lemma lem5077820 {A B : Type'} (b : B) (f : A -> B) (a : A) (h1 : (a = a) = True) : (term242 A B b f a) = (term364 A B b f a).
Proof. exact (MK_COMB (@lem5077818 A B b a h1) (@lem5077819 A B f a)). Qed.
Lemma lem5077822 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5077823 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5077822 B t2 t1). Qed.
Lemma lem5077824 {A B : Type'} (f : A -> B) (a : A) (b : B) : (term364 A B b f a) = b.
Proof. exact (@lem5077823 B (f a) b). Qed.
Lemma lem5077825 {A B : Type'} (f : A -> B) (b : B) (a : A) (h1 : (a = a) = True) : (term242 A B b f a) = b.
Proof. exact (TRANS (@lem5077820 A B b f a h1) (@lem5077824 A B f a b)). Qed.
Lemma lem5077826 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5077827 {A B : Type'} (f : A -> B) (b : B) (a : A) (h1 : (a = a) = True) : (term244 A B b f a) = (@eq B b).
Proof. exact (MK_COMB (@lem5077826 B) (@lem5077825 A B f b a h1)). Qed.
Lemma lem5077828 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5077829 {A B : Type'} (f : A -> B) (b : B) (a : A) (h1 : (a = a) = True) : ((term242 A B b f a) = b) = (b = b).
Proof. exact (MK_COMB (@lem5077827 A B f b a h1) (@lem5077828 B b)). Qed.
Lemma lem5077831 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5077832 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5077831 B x). Qed.
Lemma lem5077833 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem5077832 B b). Qed.
Lemma lem5077834 {A B : Type'} (f : A -> B) (b : B) (a : A) (h1 : (a = a) = True) : ((term242 A B b f a) = b) = True.
Proof. exact (TRANS (@lem5077829 A B f b a h1) (@lem5077833 B b)). Qed.
Lemma lem5077835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077836 {A B : Type'} (f : A -> B) (b : B) (a : A) (h1 : (a = a) = True) : (term246 A B f a b) = (and True).
Proof. exact (MK_COMB (@lem5077835) (@lem5077834 A B f b a h1)). Qed.
Lemma lem5077838 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5077839 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5077838 B x). Qed.
Lemma lem5077840 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem5077839 B b). Qed.
Lemma lem5077841 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5077842 {A B : Type'} (b : B) : (term342 A B b) = (@COND A True).
Proof. exact (MK_COMB (@lem5077841 A) (@lem5077840 B b)). Qed.
Lemma lem5077843 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5077844 {A B : Type'} (b : B) (a : A) : (term343 A B b a) = (@COND A True a).
Proof. exact (MK_COMB (@lem5077842 A B b) (@lem5077843 A a)). Qed.
Lemma lem5077845 {A B : Type'} (g : B -> A) (b : B) : (g b) = (g b).
Proof. exact (eq_refl (g b)). Qed.
Lemma lem5077846 {A B : Type'} (a : A) (g : B -> A) (b : B) : (term248 A B a g b) = (term344 A B a g b).
Proof. exact (MK_COMB (@lem5077844 A B b a) (@lem5077845 A B g b)). Qed.
Lemma lem5077848 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5077849 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem5077848 A t2 t1). Qed.
Lemma lem5077850 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term344 A B a g b) = a.
Proof. exact (@lem5077849 A (g b) a). Qed.
Lemma lem5077851 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term248 A B a g b) = a.
Proof. exact (TRANS (@lem5077846 A B a g b) (@lem5077850 A B g b a)). Qed.
Lemma lem5077852 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5077853 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term250 A B a g b) = (@eq A a).
Proof. exact (MK_COMB (@lem5077852 A) (@lem5077851 A B g b a)). Qed.
Lemma lem5077854 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5077855 {A B : Type'} (g : B -> A) (b : B) (a : A) : ((term248 A B a g b) = a) = (a = a).
Proof. exact (MK_COMB (@lem5077853 A B g b a) (@lem5077854 A a)). Qed.
Lemma lem5077857 {A : Type'} (a : A) (h1 : (a = a) = True) : (a = a) = True.
Proof. exact (h1). Qed.
Lemma lem5077858 {A B : Type'} (g : B -> A) (b : B) (a : A) (h1 : (a = a) = True) : ((term248 A B a g b) = a) = True.
Proof. exact (TRANS (@lem5077855 A B g b a) (@lem5077857 A a h1)). Qed.
Lemma lem5077859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5077860 {A B : Type'} (g : B -> A) (b : B) (a : A) (h1 : (a = a) = True) : (term252 A B g b a) = (and True).
Proof. exact (MK_COMB (@lem5077859) (@lem5077858 A B g b a h1)). Qed.
Lemma lem5077915 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term314 A B t s f b a g) = (term314 A B t s f b a g).
Proof. exact (eq_refl (term314 A B t s f b a g)). Qed.
Lemma lem5077916 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term316 A B t s f b a g) = (term365 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077860 A B g b a h1) (@lem5077915 A B t s f b a g)). Qed.
Lemma lem5077918 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5077919 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term365 A B t s f b a g) = (term314 A B t s f b a g).
Proof. exact (@lem5077918 (term314 A B t s f b a g)). Qed.
Lemma lem5077922 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term316 A B t s f b a g) = (term314 A B t s f b a g).
Proof. exact (TRANS (@lem5077916 A B t s f b g a h1) (@lem5077919 A B t s f b a g)). Qed.
Lemma lem5077923 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term317 A B t s f b a g) = (term365 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077836 A B f b a h1) (@lem5077922 A B t s f b g a h1)). Qed.
Lemma lem5077925 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5077926 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term365 A B t s f b a g) = (term314 A B t s f b a g).
Proof. exact (@lem5077925 (term314 A B t s f b a g)). Qed.
Lemma lem5077929 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term317 A B t s f b a g) = (term314 A B t s f b a g).
Proof. exact (TRANS (@lem5077923 A B t s f b g a h1) (@lem5077926 A B t s f b a g)). Qed.
Lemma lem5077930 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term199 A B t b s a f g) = (term199 A B t b s a f g).
Proof. exact (eq_refl (term199 A B t b s a f g)). Qed.
Lemma lem5077931 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term318 A B t s f b a g) = (term366 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077930 A B t b s a f g) (@lem5077929 A B t s f b g a h1)). Qed.
Lemma lem5077934 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term202 A B s a t b g f) = (term202 A B s a t b g f).
Proof. exact (eq_refl (term202 A B s a t b g f)). Qed.
Lemma lem5077935 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term319 A B t s f b a g) = (term367 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077934 A B s a t b g f) (@lem5077931 A B t s f b g a h1)). Qed.
Lemma lem5077938 {B : Type'} (b : B) (t : B -> Prop) : (term205 B b t) = (term205 B b t).
Proof. exact (eq_refl (term205 B b t)). Qed.
Lemma lem5077939 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term320 A B t s f b a g) = (term368 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077938 B b t) (@lem5077935 A B t s f b g a h1)). Qed.
Lemma lem5077942 {A : Type'} (a : A) (s : A -> Prop) : (term205 A a s) = (term205 A a s).
Proof. exact (eq_refl (term205 A a s)). Qed.
Lemma lem5077943 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term321 A B t s f b a g) = (term369 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077942 A a s) (@lem5077939 A B t s f b g a h1)). Qed.
Lemma lem5077946 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term210 A B s t) = (term210 A B s t).
Proof. exact (eq_refl (term210 A B s t)). Qed.
Lemma lem5077947 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term322 A B t s f b a g) = (term370 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077946 A B s t) (@lem5077943 A B t s f b g a h1)). Qed.
Lemma lem5077952 {B : Type'} (t : B -> Prop) : (term213 B t) = (term213 B t).
Proof. exact (eq_refl (term213 B t)). Qed.
Lemma lem5077953 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term323 A B t s f b a g) = (term371 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077952 B t) (@lem5077947 A B t s f b g a h1)). Qed.
Lemma lem5077956 {A : Type'} (s : A -> Prop) : (term213 A s) = (term213 A s).
Proof. exact (eq_refl (term213 A s)). Qed.
Lemma lem5077957 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term324 A B t s f b a g) = (term372 A B t s f b a g).
Proof. exact (MK_COMB (@lem5077956 A s) (@lem5077953 A B t s f b g a h1)). Qed.
Lemma lem5077960 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term325 A B s f b a g) = (term373 A B s f b a g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5077957 A B t s f b g a h1)). Qed.
Lemma lem5077961 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5077962 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term326 A B s f b a g) = (term374 A B s f b a g).
Proof. exact (MK_COMB (@lem5077961 B) (@lem5077960 A B s f b g a h1)). Qed.
Lemma lem5077967 {A B : Type'} (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term327 A B f b a g) = (term375 A B f b a g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5077962 A B s f b g a h1)). Qed.
Lemma lem5077968 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5077969 {A B : Type'} (f : A -> B) (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term328 A B f b a g) = (term376 A B f b a g).
Proof. exact (MK_COMB (@lem5077968 A) (@lem5077967 A B f b g a h1)). Qed.
Lemma lem5077974 {A B : Type'} (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term329 A B b a g) = (term377 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5077969 A B f b g a h1)). Qed.
Lemma lem5077975 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5077976 {A B : Type'} (b : B) (g : B -> A) (a : A) (h1 : (a = a) = True) : (term330 A B b a g) = (term378 A B b a g).
Proof. exact (MK_COMB (@lem5077975 A B) (@lem5077974 A B b g a h1)). Qed.
Lemma lem5077981 {A B : Type'} (g : B -> A) (a : A) (h1 : (a = a) = True) : (term331 A B a g) = (term379 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5077976 A B b g a h1)). Qed.
Lemma lem5077982 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5077983 {A B : Type'} (g : B -> A) (a : A) (h1 : (a = a) = True) : (term332 A B a g) = (term380 A B a g).
Proof. exact (MK_COMB (@lem5077982 B) (@lem5077981 A B g a h1)). Qed.
Lemma lem5077988 {A B : Type'} (a : A) (g : B -> A) : term381 A B a g.
Proof. exact (fun h0 : (a = a) = True => @lem5077983 A B g a h0). Qed.
Lemma lem5077989 {A B : Type'} (a : A) (g : B -> A) : term382 A B a g.
Proof. exact (conj (@lem5077774 A B a g) (@lem5077988 A B a g)). Qed.
Lemma lem5077991 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term383 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5077992 {A B : Type'} (a : A) (g : B -> A) : term384 A B a g.
Proof. exact (@lem5077991 (term332 A B a g) (term380 A B a g) (a = a) (term362 A B a g)). Qed.
Lemma lem5078007 {A B : Type'} (a : A) (g : B -> A) : (term332 A B a g) = (term385 A B a g).
Proof. exact (@lem5077992 A B a g (@lem5077989 A B a g)). Qed.
Lemma lem5078028 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term129 A B t b s a f g y) = (term129 A B t b s a f g y).
Proof. exact (eq_refl (term129 A B t b s a f g y)). Qed.
Lemma lem5078029 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term131 A B t b s a f g) = (term131 A B t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5078028 A B t b s a f g y)). Qed.
Lemma lem5078030 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5078031 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term133 A B t b s a f g) = (term133 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078030 B) (@lem5078029 A B t b s a f g)). Qed.
Lemma lem5078032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5078033 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term348 A B t b s a f g) = (term348 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078032) (@lem5078031 A B t b s a f g)). Qed.
Lemma lem5078054 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term105 A B s a t b g f x) = (term105 A B s a t b g f x).
Proof. exact (eq_refl (term105 A B s a t b g f x)). Qed.
Lemma lem5078055 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term107 A B s a t b g f) = (term107 A B s a t b g f).
Proof. exact (fun_ext (fun x : A => @lem5078054 A B s a t b g f x)). Qed.
Lemma lem5078056 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5078057 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term109 A B s a t b g f) = (term109 A B s a t b g f).
Proof. exact (MK_COMB (@lem5078056 A) (@lem5078055 A B s a t b g f)). Qed.
Lemma lem5078058 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5078059 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term202 A B s a t b g f) = (term202 A B s a t b g f).
Proof. exact (MK_COMB (@lem5078058) (@lem5078057 A B s a t b g f)). Qed.
Lemma lem5078060 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term349 A B t b s a f g) = (term349 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078059 A B s a t b g f) (@lem5078033 A B t b s a f g)). Qed.
Lemma lem5078063 {B : Type'} (b : B) (t : B -> Prop) : (term205 B b t) = (term205 B b t).
Proof. exact (eq_refl (term205 B b t)). Qed.
Lemma lem5078064 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term350 A B t b s a f g) = (term350 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078063 B b t) (@lem5078060 A B t b s a f g)). Qed.
Lemma lem5078067 {A : Type'} (a : A) (s : A -> Prop) : (term205 A a s) = (term205 A a s).
Proof. exact (eq_refl (term205 A a s)). Qed.
Lemma lem5078068 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term351 A B t b s a f g) = (term351 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078067 A a s) (@lem5078064 A B t b s a f g)). Qed.
Lemma lem5078071 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term210 A B s t) = (term210 A B s t).
Proof. exact (eq_refl (term210 A B s t)). Qed.
Lemma lem5078072 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term352 A B t b s a f g) = (term352 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078071 A B s t) (@lem5078068 A B t b s a f g)). Qed.
Lemma lem5078075 {B : Type'} (t : B -> Prop) : (term213 B t) = (term213 B t).
Proof. exact (eq_refl (term213 B t)). Qed.
Lemma lem5078076 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term353 A B t b s a f g) = (term353 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078075 B t) (@lem5078072 A B t b s a f g)). Qed.
Lemma lem5078079 {A : Type'} (s : A -> Prop) : (term213 A s) = (term213 A s).
Proof. exact (eq_refl (term213 A s)). Qed.
Lemma lem5078080 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term354 A B t b s a f g) = (term354 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078079 A s) (@lem5078076 A B t b s a f g)). Qed.
Lemma lem5078081 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term355 A B b s a f g) = (term355 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5078080 A B t b s a f g)). Qed.
Lemma lem5078082 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5078083 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term356 A B b s a f g) = (term356 A B b s a f g).
Proof. exact (MK_COMB (@lem5078082 B) (@lem5078081 A B b s a f g)). Qed.
Lemma lem5078084 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term357 A B b a f g) = (term357 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5078083 A B b s a f g)). Qed.
Lemma lem5078085 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5078086 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term358 A B b a f g) = (term358 A B b a f g).
Proof. exact (MK_COMB (@lem5078085 A) (@lem5078084 A B b a f g)). Qed.
Lemma lem5078087 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term359 A B b a g) = (term359 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5078086 A B b a f g)). Qed.
Lemma lem5078088 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5078089 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term360 A B b a g) = (term360 A B b a g).
Proof. exact (MK_COMB (@lem5078088 A B) (@lem5078087 A B b a g)). Qed.
Lemma lem5078090 {A B : Type'} (a : A) (g : B -> A) : (term361 A B a g) = (term361 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5078089 A B b a g)). Qed.
Lemma lem5078091 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5078092 {A B : Type'} (a : A) (g : B -> A) : (term362 A B a g) = (term362 A B a g).
Proof. exact (MK_COMB (@lem5078091 B) (@lem5078090 A B a g)). Qed.
Lemma lem5078095 {A : Type'} (a : A) : (term386 A a) = (term386 A a).
Proof. exact (eq_refl (term386 A a)). Qed.
Lemma lem5078096 {A B : Type'} (a : A) (g : B -> A) : (term387 A B a g) = (term387 A B a g).
Proof. exact (MK_COMB (@lem5078095 A a) (@lem5078092 A B a g)). Qed.
Lemma lem5078100 {B : Type'} (y : B) (b : B) (h1 : (y = b) = False) : (y = b) = False.
Proof. exact (h1). Qed.
Lemma lem5078101 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078102 {A B : Type'} (y : B) (b : B) (h1 : (y = b) = False) : (term388 A B y b) = (@COND A False).
Proof. exact (MK_COMB (@lem5078101 A) (@lem5078100 B y b h1)). Qed.
Lemma lem5078103 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078104 {A B : Type'} (a : A) (y : B) (b : B) (h1 : (y = b) = False) : (term389 A B y b a) = (@COND A False a).
Proof. exact (MK_COMB (@lem5078102 A B y b h1) (@lem5078103 A a)). Qed.
Lemma lem5078105 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem5078106 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term285 A B b a g y) = (term390 A B a g y).
Proof. exact (MK_COMB (@lem5078104 A B a y b h1) (@lem5078105 A B g y)). Qed.
Lemma lem5078108 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078109 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem5078108 A t1 t2). Qed.
Lemma lem5078110 {A B : Type'} (a : A) (g : B -> A) (y : B) : (term390 A B a g y) = (g y).
Proof. exact (@lem5078109 A a (g y)). Qed.
Lemma lem5078111 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term285 A B b a g y) = (g y).
Proof. exact (TRANS (@lem5078106 A B a g y b h1) (@lem5078110 A B a g y)). Qed.
Lemma lem5078112 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5078113 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term287 A B b a g y) = (term391 A B g y).
Proof. exact (MK_COMB (@lem5078112 A) (@lem5078111 A B a g y b h1)). Qed.
Lemma lem5078114 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5078115 {A B : Type'} (a : A) (g : B -> A) (s : A -> Prop) (y : B) (b : B) (h1 : (y = b) = False) : (term289 A B b a g y s) = (term392 A B g y s).
Proof. exact (MK_COMB (@lem5078113 A B a g y b h1) (@lem5078114 A s)). Qed.
Lemma lem5078116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5078117 {A B : Type'} (a : A) (g : B -> A) (s : A -> Prop) (y : B) (b : B) (h1 : (y = b) = False) : (term291 A B b a g y s) = (term393 A B g y s).
Proof. exact (MK_COMB (@lem5078116) (@lem5078115 A B a g s y b h1)). Qed.
Lemma lem5078119 {B : Type'} (y : B) (b : B) (h1 : (y = b) = False) : (y = b) = False.
Proof. exact (h1). Qed.
Lemma lem5078120 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078121 {A B : Type'} (y : B) (b : B) (h1 : (y = b) = False) : (term388 A B y b) = (@COND A False).
Proof. exact (MK_COMB (@lem5078120 A) (@lem5078119 B y b h1)). Qed.
Lemma lem5078122 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078123 {A B : Type'} (a : A) (y : B) (b : B) (h1 : (y = b) = False) : (term389 A B y b a) = (@COND A False a).
Proof. exact (MK_COMB (@lem5078121 A B y b h1) (@lem5078122 A a)). Qed.
Lemma lem5078124 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem5078125 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term285 A B b a g y) = (term390 A B a g y).
Proof. exact (MK_COMB (@lem5078123 A B a y b h1) (@lem5078124 A B g y)). Qed.
Lemma lem5078127 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078128 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem5078127 A t1 t2). Qed.
Lemma lem5078129 {A B : Type'} (a : A) (g : B -> A) (y : B) : (term390 A B a g y) = (g y).
Proof. exact (@lem5078128 A a (g y)). Qed.
Lemma lem5078130 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term285 A B b a g y) = (g y).
Proof. exact (TRANS (@lem5078125 A B a g y b h1) (@lem5078129 A B a g y)). Qed.
Lemma lem5078131 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5078132 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term295 A B b a g y) = (term394 A B g y).
Proof. exact (MK_COMB (@lem5078131 A) (@lem5078130 A B a g y b h1)). Qed.
Lemma lem5078133 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078134 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = False) : ((term285 A B b a g y) = a) = ((g y) = a).
Proof. exact (MK_COMB (@lem5078132 A B a g y b h1) (@lem5078133 A a)). Qed.
Lemma lem5078137 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078138 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = False) : (term297 A B b g y a) = (term395 A B g y a).
Proof. exact (MK_COMB (@lem5078137 B) (@lem5078134 A B g a y b h1)). Qed.
Lemma lem5078139 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078140 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = False) : (term299 A B g y a b) = (term396 A B g y a b).
Proof. exact (MK_COMB (@lem5078138 A B g a y b h1) (@lem5078139 B b)). Qed.
Lemma lem5078142 {B : Type'} (y : B) (b : B) (h1 : (y = b) = False) : (y = b) = False.
Proof. exact (h1). Qed.
Lemma lem5078143 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078144 {A B : Type'} (y : B) (b : B) (h1 : (y = b) = False) : (term388 A B y b) = (@COND A False).
Proof. exact (MK_COMB (@lem5078143 A) (@lem5078142 B y b h1)). Qed.
Lemma lem5078145 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078146 {A B : Type'} (a : A) (y : B) (b : B) (h1 : (y = b) = False) : (term389 A B y b a) = (@COND A False a).
Proof. exact (MK_COMB (@lem5078144 A B y b h1) (@lem5078145 A a)). Qed.
Lemma lem5078147 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem5078148 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term285 A B b a g y) = (term390 A B a g y).
Proof. exact (MK_COMB (@lem5078146 A B a y b h1) (@lem5078147 A B g y)). Qed.
Lemma lem5078150 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078151 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem5078150 A t1 t2). Qed.
Lemma lem5078152 {A B : Type'} (a : A) (g : B -> A) (y : B) : (term390 A B a g y) = (g y).
Proof. exact (@lem5078151 A a (g y)). Qed.
Lemma lem5078153 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term285 A B b a g y) = (g y).
Proof. exact (TRANS (@lem5078148 A B a g y b h1) (@lem5078152 A B a g y)). Qed.
Lemma lem5078154 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5078155 {A B : Type'} (a : A) (f : A -> B) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term301 A B f b a g y) = (term124 A B f g y).
Proof. exact (MK_COMB (@lem5078154 A B f) (@lem5078153 A B a g y b h1)). Qed.
Lemma lem5078156 {A B : Type'} (a : A) (f : A -> B) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term302 A B f b a g y) = (term397 A B a b f g y).
Proof. exact (MK_COMB (@lem5078140 A B g a y b h1) (@lem5078155 A B a f g y b h1)). Qed.
Lemma lem5078159 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5078160 {A B : Type'} (a : A) (f : A -> B) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term304 A B f b a g y) = (term398 A B a b f g y).
Proof. exact (MK_COMB (@lem5078159 B) (@lem5078156 A B a f g y b h1)). Qed.
Lemma lem5078161 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5078162 {A B : Type'} (a : A) (f : A -> B) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : ((term302 A B f b a g y) = y) = ((term397 A B a b f g y) = y).
Proof. exact (MK_COMB (@lem5078160 A B a f g y b h1) (@lem5078161 B y)). Qed.
Lemma lem5078165 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term306 A B s f b a g y) = (term399 A B s a b f g y).
Proof. exact (MK_COMB (@lem5078117 A B a g s y b h1) (@lem5078162 A B a f g y b h1)). Qed.
Lemma lem5078168 {B : Type'} (y : B) (t : B -> Prop) : (term205 B y t) = (term205 B y t).
Proof. exact (eq_refl (term205 B y t)). Qed.
Lemma lem5078169 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = False) : (term308 A B t s f b a g y) = (term400 A B t s a b f g y).
Proof. exact (MK_COMB (@lem5078168 B y t) (@lem5078165 A B s a f g y b h1)). Qed.
Lemma lem5078172 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (b : B) (f : A -> B) (g : B -> A) (y : B) : term401 A B t s a b f g y.
Proof. exact (fun h0 : (y = b) = False => @lem5078169 A B t s a f g y b h0). Qed.
Lemma lem5078174 {B : Type'} (y : B) (b : B) (h1 : (y = b) = True) : (y = b) = True.
Proof. exact (h1). Qed.
Lemma lem5078175 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078176 {A B : Type'} (y : B) (b : B) (h1 : (y = b) = True) : (term388 A B y b) = (@COND A True).
Proof. exact (MK_COMB (@lem5078175 A) (@lem5078174 B y b h1)). Qed.
Lemma lem5078177 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078178 {A B : Type'} (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term389 A B y b a) = (@COND A True a).
Proof. exact (MK_COMB (@lem5078176 A B y b h1) (@lem5078177 A a)). Qed.
Lemma lem5078179 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem5078180 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = True) : (term285 A B b a g y) = (term344 A B a g y).
Proof. exact (MK_COMB (@lem5078178 A B a y b h1) (@lem5078179 A B g y)). Qed.
Lemma lem5078182 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078183 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem5078182 A t2 t1). Qed.
Lemma lem5078184 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term344 A B a g y) = a.
Proof. exact (@lem5078183 A (g y) a). Qed.
Lemma lem5078185 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term285 A B b a g y) = a.
Proof. exact (TRANS (@lem5078180 A B a g y b h1) (@lem5078184 A B g y a)). Qed.
Lemma lem5078186 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5078187 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term287 A B b a g y) = (@IN A a).
Proof. exact (MK_COMB (@lem5078186 A) (@lem5078185 A B g a y b h1)). Qed.
Lemma lem5078188 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5078189 {A B : Type'} (g : B -> A) (a : A) (s : A -> Prop) (y : B) (b : B) (h1 : (y = b) = True) : (term289 A B b a g y s) = (@IN A a s).
Proof. exact (MK_COMB (@lem5078187 A B g a y b h1) (@lem5078188 A s)). Qed.
Lemma lem5078190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5078191 {A B : Type'} (g : B -> A) (a : A) (s : A -> Prop) (y : B) (b : B) (h1 : (y = b) = True) : (term291 A B b a g y s) = (term402 A a s).
Proof. exact (MK_COMB (@lem5078190) (@lem5078189 A B g a s y b h1)). Qed.
Lemma lem5078193 {B : Type'} (y : B) (b : B) (h1 : (y = b) = True) : (y = b) = True.
Proof. exact (h1). Qed.
Lemma lem5078194 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078195 {A B : Type'} (y : B) (b : B) (h1 : (y = b) = True) : (term388 A B y b) = (@COND A True).
Proof. exact (MK_COMB (@lem5078194 A) (@lem5078193 B y b h1)). Qed.
Lemma lem5078196 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078197 {A B : Type'} (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term389 A B y b a) = (@COND A True a).
Proof. exact (MK_COMB (@lem5078195 A B y b h1) (@lem5078196 A a)). Qed.
Lemma lem5078198 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem5078199 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = True) : (term285 A B b a g y) = (term344 A B a g y).
Proof. exact (MK_COMB (@lem5078197 A B a y b h1) (@lem5078198 A B g y)). Qed.
Lemma lem5078201 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078202 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem5078201 A t2 t1). Qed.
Lemma lem5078203 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term344 A B a g y) = a.
Proof. exact (@lem5078202 A (g y) a). Qed.
Lemma lem5078204 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term285 A B b a g y) = a.
Proof. exact (TRANS (@lem5078199 A B a g y b h1) (@lem5078203 A B g y a)). Qed.
Lemma lem5078205 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5078206 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term295 A B b a g y) = (@eq A a).
Proof. exact (MK_COMB (@lem5078205 A) (@lem5078204 A B g a y b h1)). Qed.
Lemma lem5078207 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078208 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : ((term285 A B b a g y) = a) = (a = a).
Proof. exact (MK_COMB (@lem5078206 A B g a y b h1) (@lem5078207 A a)). Qed.
Lemma lem5078210 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5078211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem5078210 A x). Qed.
Lemma lem5078212 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem5078211 A a). Qed.
Lemma lem5078213 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : ((term285 A B b a g y) = a) = True.
Proof. exact (TRANS (@lem5078208 A B g a y b h1) (@lem5078212 A a)). Qed.
Lemma lem5078214 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078215 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term297 A B b g y a) = (@COND B True).
Proof. exact (MK_COMB (@lem5078214 B) (@lem5078213 A B g a y b h1)). Qed.
Lemma lem5078216 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078217 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term299 A B g y a b) = (@COND B True b).
Proof. exact (MK_COMB (@lem5078215 A B g a y b h1) (@lem5078216 B b)). Qed.
Lemma lem5078219 {B : Type'} (y : B) (b : B) (h1 : (y = b) = True) : (y = b) = True.
Proof. exact (h1). Qed.
Lemma lem5078220 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078221 {A B : Type'} (y : B) (b : B) (h1 : (y = b) = True) : (term388 A B y b) = (@COND A True).
Proof. exact (MK_COMB (@lem5078220 A) (@lem5078219 B y b h1)). Qed.
Lemma lem5078222 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078223 {A B : Type'} (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term389 A B y b a) = (@COND A True a).
Proof. exact (MK_COMB (@lem5078221 A B y b h1) (@lem5078222 A a)). Qed.
Lemma lem5078224 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem5078225 {A B : Type'} (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = True) : (term285 A B b a g y) = (term344 A B a g y).
Proof. exact (MK_COMB (@lem5078223 A B a y b h1) (@lem5078224 A B g y)). Qed.
Lemma lem5078227 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078228 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem5078227 A t2 t1). Qed.
Lemma lem5078229 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term344 A B a g y) = a.
Proof. exact (@lem5078228 A (g y) a). Qed.
Lemma lem5078230 {A B : Type'} (g : B -> A) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term285 A B b a g y) = a.
Proof. exact (TRANS (@lem5078225 A B a g y b h1) (@lem5078229 A B g y a)). Qed.
Lemma lem5078231 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5078232 {A B : Type'} (g : B -> A) (f : A -> B) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term301 A B f b a g y) = (f a).
Proof. exact (MK_COMB (@lem5078231 A B f) (@lem5078230 A B g a y b h1)). Qed.
Lemma lem5078233 {A B : Type'} (g : B -> A) (f : A -> B) (a : A) (y : B) (b : B) (h1 : (y = b) = True) : (term302 A B f b a g y) = (term364 A B b f a).
Proof. exact (MK_COMB (@lem5078217 A B g a y b h1) (@lem5078232 A B g f a y b h1)). Qed.
Lemma lem5078235 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078236 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5078235 B t2 t1). Qed.
Lemma lem5078237 {A B : Type'} (f : A -> B) (a : A) (b : B) : (term364 A B b f a) = b.
Proof. exact (@lem5078236 B (f a) b). Qed.
Lemma lem5078238 {A B : Type'} (f : A -> B) (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = True) : (term302 A B f b a g y) = b.
Proof. exact (TRANS (@lem5078233 A B g f a y b h1) (@lem5078237 A B f a b)). Qed.
Lemma lem5078239 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5078240 {A B : Type'} (f : A -> B) (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = True) : (term304 A B f b a g y) = (@eq B b).
Proof. exact (MK_COMB (@lem5078239 B) (@lem5078238 A B f a g y b h1)). Qed.
Lemma lem5078241 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5078242 {A B : Type'} (f : A -> B) (a : A) (g : B -> A) (y : B) (b : B) (h1 : (y = b) = True) : ((term302 A B f b a g y) = y) = (b = y).
Proof. exact (MK_COMB (@lem5078240 A B f a g y b h1) (@lem5078241 B y)). Qed.
Lemma lem5078245 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (y : B) (b : B) (h1 : (y = b) = True) : (term306 A B s f b a g y) = (term403 A B a s b y).
Proof. exact (MK_COMB (@lem5078191 A B g a s y b h1) (@lem5078242 A B f a g y b h1)). Qed.
Lemma lem5078248 {B : Type'} (y : B) (t : B -> Prop) : (term205 B y t) = (term205 B y t).
Proof. exact (eq_refl (term205 B y t)). Qed.
Lemma lem5078249 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (y : B) (b : B) (h1 : (y = b) = True) : (term308 A B t s f b a g y) = (term404 A B t a s b y).
Proof. exact (MK_COMB (@lem5078248 B y t) (@lem5078245 A B f g a s y b h1)). Qed.
Lemma lem5078252 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : term405 A B f g t a s b y.
Proof. exact (fun h0 : (y = b) = True => @lem5078249 A B f g t a s y b h0). Qed.
Lemma lem5078253 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : term406 A B f g t a s b y.
Proof. exact (conj (@lem5078172 A B t s a b f g y) (@lem5078252 A B f g t a s b y)). Qed.
Lemma lem5078255 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term383 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5078256 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (b : B) (f : A -> B) (g : B -> A) (y : B) : term407 A B t s a b f g y.
Proof. exact (@lem5078255 (term308 A B t s f b a g y) (term404 A B t a s b y) (y = b) (term400 A B t s a b f g y)). Qed.
Lemma lem5078271 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term308 A B t s f b a g y) = (term408 A B t s a b f g y).
Proof. exact (@lem5078256 A B t s a b f g y (@lem5078253 A B f g t a s b y)). Qed.
Lemma lem5078287 {A B : Type'} (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : ((g y) = a) = False.
Proof. exact (h1). Qed.
Lemma lem5078288 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078289 {A B : Type'} (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term395 A B g y a) = (@COND B False).
Proof. exact (MK_COMB (@lem5078288 B) (@lem5078287 A B g y a h1)). Qed.
Lemma lem5078290 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078291 {A B : Type'} (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term396 A B g y a b) = (@COND B False b).
Proof. exact (MK_COMB (@lem5078289 A B g y a h1) (@lem5078290 B b)). Qed.
Lemma lem5078292 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term124 A B f g y) = (term124 A B f g y).
Proof. exact (eq_refl (term124 A B f g y)). Qed.
Lemma lem5078293 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term397 A B a b f g y) = (term409 A B b f g y).
Proof. exact (MK_COMB (@lem5078291 A B b g y a h1) (@lem5078292 A B f g y)). Qed.
Lemma lem5078295 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078296 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5078295 B t1 t2). Qed.
Lemma lem5078297 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (y : B) : (term409 A B b f g y) = (term124 A B f g y).
Proof. exact (@lem5078296 B b (term124 A B f g y)). Qed.
Lemma lem5078298 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term397 A B a b f g y) = (term124 A B f g y).
Proof. exact (TRANS (@lem5078293 A B b f g y a h1) (@lem5078297 A B b f g y)). Qed.
Lemma lem5078299 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5078300 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term398 A B a b f g y) = (term410 A B f g y).
Proof. exact (MK_COMB (@lem5078299 B) (@lem5078298 A B b f g y a h1)). Qed.
Lemma lem5078301 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5078302 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : ((term397 A B a b f g y) = y) = ((term124 A B f g y) = y).
Proof. exact (MK_COMB (@lem5078300 A B b f g y a h1) (@lem5078301 B y)). Qed.
Lemma lem5078305 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term393 A B g y s) = (term393 A B g y s).
Proof. exact (eq_refl (term393 A B g y s)). Qed.
Lemma lem5078306 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term399 A B s a b f g y) = (term411 A B s f g y).
Proof. exact (MK_COMB (@lem5078305 A B g y s) (@lem5078302 A B b f g y a h1)). Qed.
Lemma lem5078309 {B : Type'} (y : B) (t : B -> Prop) : (term205 B y t) = (term205 B y t).
Proof. exact (eq_refl (term205 B y t)). Qed.
Lemma lem5078310 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term400 A B t s a b f g y) = (term412 A B t s f g y).
Proof. exact (MK_COMB (@lem5078309 B y t) (@lem5078306 A B b s f g y a h1)). Qed.
Lemma lem5078313 {B : Type'} (y : B) (b : B) : (term413 B y b) = (term413 B y b).
Proof. exact (eq_refl (term413 B y b)). Qed.
Lemma lem5078314 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term414 A B t s a b f g y) = (term415 A B b t s f g y).
Proof. exact (MK_COMB (@lem5078313 B y b) (@lem5078310 A B b t s f g y a h1)). Qed.
Lemma lem5078317 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term416 A B t a s b y) = (term416 A B t a s b y).
Proof. exact (eq_refl (term416 A B t a s b y)). Qed.
Lemma lem5078318 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = False) : (term408 A B t s a b f g y) = (term417 A B a b t s f g y).
Proof. exact (MK_COMB (@lem5078317 A B t a s b y) (@lem5078314 A B b t s f g y a h1)). Qed.
Lemma lem5078321 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : term418 A B a b t s f g y.
Proof. exact (fun h0 : ((g y) = a) = False => @lem5078318 A B b t s f g y a h0). Qed.
Lemma lem5078335 {A B : Type'} (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : ((g y) = a) = True.
Proof. exact (h1). Qed.
Lemma lem5078336 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078337 {A B : Type'} (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term395 A B g y a) = (@COND B True).
Proof. exact (MK_COMB (@lem5078336 B) (@lem5078335 A B g y a h1)). Qed.
Lemma lem5078338 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078339 {A B : Type'} (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term396 A B g y a b) = (@COND B True b).
Proof. exact (MK_COMB (@lem5078337 A B g y a h1) (@lem5078338 B b)). Qed.
Lemma lem5078340 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term124 A B f g y) = (term124 A B f g y).
Proof. exact (eq_refl (term124 A B f g y)). Qed.
Lemma lem5078341 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term397 A B a b f g y) = (term419 A B b f g y).
Proof. exact (MK_COMB (@lem5078339 A B b g y a h1) (@lem5078340 A B f g y)). Qed.
Lemma lem5078343 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078344 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5078343 B t2 t1). Qed.
Lemma lem5078345 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (b : B) : (term419 A B b f g y) = b.
Proof. exact (@lem5078344 B (term124 A B f g y) b). Qed.
Lemma lem5078346 {A B : Type'} (f : A -> B) (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term397 A B a b f g y) = b.
Proof. exact (TRANS (@lem5078341 A B b f g y a h1) (@lem5078345 A B f g y b)). Qed.
Lemma lem5078347 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5078348 {A B : Type'} (f : A -> B) (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term398 A B a b f g y) = (@eq B b).
Proof. exact (MK_COMB (@lem5078347 B) (@lem5078346 A B f b g y a h1)). Qed.
Lemma lem5078349 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5078350 {A B : Type'} (f : A -> B) (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : ((term397 A B a b f g y) = y) = (b = y).
Proof. exact (MK_COMB (@lem5078348 A B f b g y a h1) (@lem5078349 B y)). Qed.
Lemma lem5078353 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term393 A B g y s) = (term393 A B g y s).
Proof. exact (eq_refl (term393 A B g y s)). Qed.
Lemma lem5078354 {A B : Type'} (f : A -> B) (s : A -> Prop) (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term399 A B s a b f g y) = (term420 A B g s b y).
Proof. exact (MK_COMB (@lem5078353 A B g y s) (@lem5078350 A B f b g y a h1)). Qed.
Lemma lem5078357 {B : Type'} (y : B) (t : B -> Prop) : (term205 B y t) = (term205 B y t).
Proof. exact (eq_refl (term205 B y t)). Qed.
Lemma lem5078358 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term400 A B t s a b f g y) = (term421 A B t g s b y).
Proof. exact (MK_COMB (@lem5078357 B y t) (@lem5078354 A B f s b g y a h1)). Qed.
Lemma lem5078361 {B : Type'} (y : B) (b : B) : (term413 B y b) = (term413 B y b).
Proof. exact (eq_refl (term413 B y b)). Qed.
Lemma lem5078362 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term414 A B t s a b f g y) = (term422 A B t g s b y).
Proof. exact (MK_COMB (@lem5078361 B y b) (@lem5078358 A B f t s b g y a h1)). Qed.
Lemma lem5078365 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term416 A B t a s b y) = (term416 A B t a s b y).
Proof. exact (eq_refl (term416 A B t a s b y)). Qed.
Lemma lem5078366 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (b : B) (g : B -> A) (y : B) (a : A) (h1 : ((g y) = a) = True) : (term408 A B t s a b f g y) = (term423 A B a t g s b y).
Proof. exact (MK_COMB (@lem5078365 A B t a s b y) (@lem5078362 A B f t s b g y a h1)). Qed.
Lemma lem5078369 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : term424 A B f a t g s b y.
Proof. exact (fun h0 : ((g y) = a) = True => @lem5078366 A B f t s b g y a h0). Qed.
Lemma lem5078370 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : term425 A B f a t g s b y.
Proof. exact (conj (@lem5078321 A B a b t s f g y) (@lem5078369 A B f a t g s b y)). Qed.
Lemma lem5078372 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term383 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5078373 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : term426 A B a b t s f g y.
Proof. exact (@lem5078372 (term408 A B t s a b f g y) (term423 A B a t g s b y) ((g y) = a) (term417 A B a b t s f g y)). Qed.
Lemma lem5078466 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term408 A B t s a b f g y) = (term427 A B a b t s f g y).
Proof. exact (@lem5078373 A B a b t s f g y (@lem5078370 A B f a t g s b y)). Qed.
Lemma lem5078467 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (y : B) : (term428 A B t s f b a g y) = (term428 A B t s f b a g y).
Proof. exact (eq_refl (term428 A B t s f b a g y)). Qed.
Lemma lem5078468 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : ((term308 A B t s f b a g y) = (term408 A B t s a b f g y)) = ((term308 A B t s f b a g y) = (term427 A B a b t s f g y)).
Proof. exact (MK_COMB (@lem5078467 A B t s f b a g y) (@lem5078466 A B a b t s f g y)). Qed.
Lemma lem5078469 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term308 A B t s f b a g y) = (term427 A B a b t s f g y).
Proof. exact (EQ_MP (@lem5078468 A B a b t s f g y) (@lem5078271 A B t s a b f g y)). Qed.
Lemma lem5078470 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term310 A B t s f b a g) = (term429 A B a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5078469 A B a b t s f g y)). Qed.
Lemma lem5078471 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5078472 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term312 A B t s f b a g) = (term430 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078471 B) (@lem5078470 A B a b t s f g)). Qed.
Lemma lem5078476 {A : Type'} (x : A) (a : A) (h1 : (x = a) = False) : (x = a) = False.
Proof. exact (h1). Qed.
Lemma lem5078477 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078478 {A B : Type'} (x : A) (a : A) (h1 : (x = a) = False) : (term431 A B x a) = (@COND B False).
Proof. exact (MK_COMB (@lem5078477 B) (@lem5078476 A x a h1)). Qed.
Lemma lem5078479 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078480 {A B : Type'} (b : B) (x : A) (a : A) (h1 : (x = a) = False) : (term432 A B x a b) = (@COND B False b).
Proof. exact (MK_COMB (@lem5078478 A B x a h1) (@lem5078479 B b)). Qed.
Lemma lem5078481 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5078482 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term254 A B a b f x) = (term339 A B b f x).
Proof. exact (MK_COMB (@lem5078480 A B b x a h1) (@lem5078481 A B f x)). Qed.
Lemma lem5078484 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078485 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5078484 B t1 t2). Qed.
Lemma lem5078486 {A B : Type'} (b : B) (f : A -> B) (x : A) : (term339 A B b f x) = (f x).
Proof. exact (@lem5078485 B b (f x)). Qed.
Lemma lem5078487 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term254 A B a b f x) = (f x).
Proof. exact (TRANS (@lem5078482 A B b f x a h1) (@lem5078486 A B b f x)). Qed.
Lemma lem5078488 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5078489 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term256 A B a b f x) = (term433 A B f x).
Proof. exact (MK_COMB (@lem5078488 B) (@lem5078487 A B b f x a h1)). Qed.
Lemma lem5078490 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5078491 {A B : Type'} (b : B) (f : A -> B) (t : B -> Prop) (x : A) (a : A) (h1 : (x = a) = False) : (term258 A B a b f x t) = (term434 A B f x t).
Proof. exact (MK_COMB (@lem5078489 A B b f x a h1) (@lem5078490 B t)). Qed.
Lemma lem5078492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5078493 {A B : Type'} (b : B) (f : A -> B) (t : B -> Prop) (x : A) (a : A) (h1 : (x = a) = False) : (term260 A B a b f x t) = (term435 A B f x t).
Proof. exact (MK_COMB (@lem5078492) (@lem5078491 A B b f t x a h1)). Qed.
Lemma lem5078495 {A : Type'} (x : A) (a : A) (h1 : (x = a) = False) : (x = a) = False.
Proof. exact (h1). Qed.
Lemma lem5078496 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078497 {A B : Type'} (x : A) (a : A) (h1 : (x = a) = False) : (term431 A B x a) = (@COND B False).
Proof. exact (MK_COMB (@lem5078496 B) (@lem5078495 A x a h1)). Qed.
Lemma lem5078498 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078499 {A B : Type'} (b : B) (x : A) (a : A) (h1 : (x = a) = False) : (term432 A B x a b) = (@COND B False b).
Proof. exact (MK_COMB (@lem5078497 A B x a h1) (@lem5078498 B b)). Qed.
Lemma lem5078500 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5078501 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term254 A B a b f x) = (term339 A B b f x).
Proof. exact (MK_COMB (@lem5078499 A B b x a h1) (@lem5078500 A B f x)). Qed.
Lemma lem5078503 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078504 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5078503 B t1 t2). Qed.
Lemma lem5078505 {A B : Type'} (b : B) (f : A -> B) (x : A) : (term339 A B b f x) = (f x).
Proof. exact (@lem5078504 B b (f x)). Qed.
Lemma lem5078506 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term254 A B a b f x) = (f x).
Proof. exact (TRANS (@lem5078501 A B b f x a h1) (@lem5078505 A B b f x)). Qed.
Lemma lem5078507 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5078508 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term264 A B a b f x) = (term340 A B f x).
Proof. exact (MK_COMB (@lem5078507 B) (@lem5078506 A B b f x a h1)). Qed.
Lemma lem5078509 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078510 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = False) : ((term254 A B a b f x) = b) = ((f x) = b).
Proof. exact (MK_COMB (@lem5078508 A B b f x a h1) (@lem5078509 B b)). Qed.
Lemma lem5078513 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078514 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = False) : (term266 A B a f x b) = (term436 A B f x b).
Proof. exact (MK_COMB (@lem5078513 A) (@lem5078510 A B f b x a h1)). Qed.
Lemma lem5078515 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078516 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = False) : (term268 A B f x b a) = (term437 A B f x b a).
Proof. exact (MK_COMB (@lem5078514 A B f b x a h1) (@lem5078515 A a)). Qed.
Lemma lem5078518 {A : Type'} (x : A) (a : A) (h1 : (x = a) = False) : (x = a) = False.
Proof. exact (h1). Qed.
Lemma lem5078519 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078520 {A B : Type'} (x : A) (a : A) (h1 : (x = a) = False) : (term431 A B x a) = (@COND B False).
Proof. exact (MK_COMB (@lem5078519 B) (@lem5078518 A x a h1)). Qed.
Lemma lem5078521 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078522 {A B : Type'} (b : B) (x : A) (a : A) (h1 : (x = a) = False) : (term432 A B x a b) = (@COND B False b).
Proof. exact (MK_COMB (@lem5078520 A B x a h1) (@lem5078521 B b)). Qed.
Lemma lem5078523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5078524 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term254 A B a b f x) = (term339 A B b f x).
Proof. exact (MK_COMB (@lem5078522 A B b x a h1) (@lem5078523 A B f x)). Qed.
Lemma lem5078526 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078527 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5078526 B t1 t2). Qed.
Lemma lem5078528 {A B : Type'} (b : B) (f : A -> B) (x : A) : (term339 A B b f x) = (f x).
Proof. exact (@lem5078527 B b (f x)). Qed.
Lemma lem5078529 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term254 A B a b f x) = (f x).
Proof. exact (TRANS (@lem5078524 A B b f x a h1) (@lem5078528 A B b f x)). Qed.
Lemma lem5078530 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5078531 {A B : Type'} (b : B) (g : B -> A) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term270 A B g a b f x) = (term100 A B g f x).
Proof. exact (MK_COMB (@lem5078530 A B g) (@lem5078529 A B b f x a h1)). Qed.
Lemma lem5078532 {A B : Type'} (b : B) (g : B -> A) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term271 A B g a b f x) = (term438 A B b a g f x).
Proof. exact (MK_COMB (@lem5078516 A B f b x a h1) (@lem5078531 A B b g f x a h1)). Qed.
Lemma lem5078535 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5078536 {A B : Type'} (b : B) (g : B -> A) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term273 A B g a b f x) = (term439 A B b a g f x).
Proof. exact (MK_COMB (@lem5078535 A) (@lem5078532 A B b g f x a h1)). Qed.
Lemma lem5078537 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5078538 {A B : Type'} (b : B) (g : B -> A) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : ((term271 A B g a b f x) = x) = ((term438 A B b a g f x) = x).
Proof. exact (MK_COMB (@lem5078536 A B b g f x a h1) (@lem5078537 A x)). Qed.
Lemma lem5078541 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term275 A B t g a b f x) = (term440 A B t b a g f x).
Proof. exact (MK_COMB (@lem5078493 A B b f t x a h1) (@lem5078538 A B b g f x a h1)). Qed.
Lemma lem5078544 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (term205 A x s).
Proof. exact (eq_refl (term205 A x s)). Qed.
Lemma lem5078545 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = False) : (term277 A B s t g a b f x) = (term441 A B s t b a g f x).
Proof. exact (MK_COMB (@lem5078544 A x s) (@lem5078541 A B t b g f x a h1)). Qed.
Lemma lem5078548 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (a : A) (g : B -> A) (f : A -> B) (x : A) : term442 A B s t b a g f x.
Proof. exact (fun h0 : (x = a) = False => @lem5078545 A B s t b g f x a h0). Qed.
Lemma lem5078550 {A : Type'} (x : A) (a : A) (h1 : (x = a) = True) : (x = a) = True.
Proof. exact (h1). Qed.
Lemma lem5078551 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078552 {A B : Type'} (x : A) (a : A) (h1 : (x = a) = True) : (term431 A B x a) = (@COND B True).
Proof. exact (MK_COMB (@lem5078551 B) (@lem5078550 A x a h1)). Qed.
Lemma lem5078553 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078554 {A B : Type'} (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term432 A B x a b) = (@COND B True b).
Proof. exact (MK_COMB (@lem5078552 A B x a h1) (@lem5078553 B b)). Qed.
Lemma lem5078555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5078556 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = True) : (term254 A B a b f x) = (term364 A B b f x).
Proof. exact (MK_COMB (@lem5078554 A B b x a h1) (@lem5078555 A B f x)). Qed.
Lemma lem5078558 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078559 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5078558 B t2 t1). Qed.
Lemma lem5078560 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term364 A B b f x) = b.
Proof. exact (@lem5078559 B (f x) b). Qed.
Lemma lem5078561 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term254 A B a b f x) = b.
Proof. exact (TRANS (@lem5078556 A B b f x a h1) (@lem5078560 A B f x b)). Qed.
Lemma lem5078562 {B : Type'} : (@IN B) = (@IN B).
Proof. exact (eq_refl (@IN B)). Qed.
Lemma lem5078563 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term256 A B a b f x) = (@IN B b).
Proof. exact (MK_COMB (@lem5078562 B) (@lem5078561 A B f b x a h1)). Qed.
Lemma lem5078564 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5078565 {A B : Type'} (f : A -> B) (b : B) (t : B -> Prop) (x : A) (a : A) (h1 : (x = a) = True) : (term258 A B a b f x t) = (@IN B b t).
Proof. exact (MK_COMB (@lem5078563 A B f b x a h1) (@lem5078564 B t)). Qed.
Lemma lem5078566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5078567 {A B : Type'} (f : A -> B) (b : B) (t : B -> Prop) (x : A) (a : A) (h1 : (x = a) = True) : (term260 A B a b f x t) = (term402 B b t).
Proof. exact (MK_COMB (@lem5078566) (@lem5078565 A B f b t x a h1)). Qed.
Lemma lem5078569 {A : Type'} (x : A) (a : A) (h1 : (x = a) = True) : (x = a) = True.
Proof. exact (h1). Qed.
Lemma lem5078570 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078571 {A B : Type'} (x : A) (a : A) (h1 : (x = a) = True) : (term431 A B x a) = (@COND B True).
Proof. exact (MK_COMB (@lem5078570 B) (@lem5078569 A x a h1)). Qed.
Lemma lem5078572 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078573 {A B : Type'} (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term432 A B x a b) = (@COND B True b).
Proof. exact (MK_COMB (@lem5078571 A B x a h1) (@lem5078572 B b)). Qed.
Lemma lem5078574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5078575 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = True) : (term254 A B a b f x) = (term364 A B b f x).
Proof. exact (MK_COMB (@lem5078573 A B b x a h1) (@lem5078574 A B f x)). Qed.
Lemma lem5078577 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078578 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5078577 B t2 t1). Qed.
Lemma lem5078579 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term364 A B b f x) = b.
Proof. exact (@lem5078578 B (f x) b). Qed.
Lemma lem5078580 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term254 A B a b f x) = b.
Proof. exact (TRANS (@lem5078575 A B b f x a h1) (@lem5078579 A B f x b)). Qed.
Lemma lem5078581 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5078582 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term264 A B a b f x) = (@eq B b).
Proof. exact (MK_COMB (@lem5078581 B) (@lem5078580 A B f b x a h1)). Qed.
Lemma lem5078583 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078584 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : ((term254 A B a b f x) = b) = (b = b).
Proof. exact (MK_COMB (@lem5078582 A B f b x a h1) (@lem5078583 B b)). Qed.
Lemma lem5078586 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5078587 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5078586 B x). Qed.
Lemma lem5078588 {B : Type'} (b : B) : (b = b) = True.
Proof. exact (@lem5078587 B b). Qed.
Lemma lem5078589 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : ((term254 A B a b f x) = b) = True.
Proof. exact (TRANS (@lem5078584 A B f b x a h1) (@lem5078588 B b)). Qed.
Lemma lem5078590 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078591 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term266 A B a f x b) = (@COND A True).
Proof. exact (MK_COMB (@lem5078590 A) (@lem5078589 A B f b x a h1)). Qed.
Lemma lem5078592 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078593 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term268 A B f x b a) = (@COND A True a).
Proof. exact (MK_COMB (@lem5078591 A B f b x a h1) (@lem5078592 A a)). Qed.
Lemma lem5078595 {A : Type'} (x : A) (a : A) (h1 : (x = a) = True) : (x = a) = True.
Proof. exact (h1). Qed.
Lemma lem5078596 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem5078597 {A B : Type'} (x : A) (a : A) (h1 : (x = a) = True) : (term431 A B x a) = (@COND B True).
Proof. exact (MK_COMB (@lem5078596 B) (@lem5078595 A x a h1)). Qed.
Lemma lem5078598 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5078599 {A B : Type'} (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term432 A B x a b) = (@COND B True b).
Proof. exact (MK_COMB (@lem5078597 A B x a h1) (@lem5078598 B b)). Qed.
Lemma lem5078600 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem5078601 {A B : Type'} (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = True) : (term254 A B a b f x) = (term364 A B b f x).
Proof. exact (MK_COMB (@lem5078599 A B b x a h1) (@lem5078600 A B f x)). Qed.
Lemma lem5078603 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078604 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5078603 B t2 t1). Qed.
Lemma lem5078605 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term364 A B b f x) = b.
Proof. exact (@lem5078604 B (f x) b). Qed.
Lemma lem5078606 {A B : Type'} (f : A -> B) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term254 A B a b f x) = b.
Proof. exact (TRANS (@lem5078601 A B b f x a h1) (@lem5078605 A B f x b)). Qed.
Lemma lem5078607 {A B : Type'} (g : B -> A) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5078608 {A B : Type'} (f : A -> B) (g : B -> A) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term270 A B g a b f x) = (g b).
Proof. exact (MK_COMB (@lem5078607 A B g) (@lem5078606 A B f b x a h1)). Qed.
Lemma lem5078609 {A B : Type'} (f : A -> B) (g : B -> A) (b : B) (x : A) (a : A) (h1 : (x = a) = True) : (term271 A B g a b f x) = (term344 A B a g b).
Proof. exact (MK_COMB (@lem5078593 A B f b x a h1) (@lem5078608 A B f g b x a h1)). Qed.
Lemma lem5078611 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078612 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem5078611 A t2 t1). Qed.
Lemma lem5078613 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term344 A B a g b) = a.
Proof. exact (@lem5078612 A (g b) a). Qed.
Lemma lem5078614 {A B : Type'} (g : B -> A) (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = True) : (term271 A B g a b f x) = a.
Proof. exact (TRANS (@lem5078609 A B f g b x a h1) (@lem5078613 A B g b a)). Qed.
Lemma lem5078615 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5078616 {A B : Type'} (g : B -> A) (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = True) : (term273 A B g a b f x) = (@eq A a).
Proof. exact (MK_COMB (@lem5078615 A) (@lem5078614 A B g b f x a h1)). Qed.
Lemma lem5078617 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5078618 {A B : Type'} (g : B -> A) (b : B) (f : A -> B) (x : A) (a : A) (h1 : (x = a) = True) : ((term271 A B g a b f x) = x) = (a = x).
Proof. exact (MK_COMB (@lem5078616 A B g b f x a h1) (@lem5078617 A x)). Qed.
Lemma lem5078621 {A B : Type'} (g : B -> A) (f : A -> B) (b : B) (t : B -> Prop) (x : A) (a : A) (h1 : (x = a) = True) : (term275 A B t g a b f x) = (term443 A B b t a x).
Proof. exact (MK_COMB (@lem5078567 A B f b t x a h1) (@lem5078618 A B g b f x a h1)). Qed.
Lemma lem5078624 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (term205 A x s).
Proof. exact (eq_refl (term205 A x s)). Qed.
Lemma lem5078625 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (b : B) (t : B -> Prop) (x : A) (a : A) (h1 : (x = a) = True) : (term277 A B s t g a b f x) = (term444 A B s b t a x).
Proof. exact (MK_COMB (@lem5078624 A x s) (@lem5078621 A B g f b t x a h1)). Qed.
Lemma lem5078628 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : term445 A B g f s b t a x.
Proof. exact (fun h0 : (x = a) = True => @lem5078625 A B g f s b t x a h0). Qed.
Lemma lem5078629 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : term446 A B g f s b t a x.
Proof. exact (conj (@lem5078548 A B s t b a g f x) (@lem5078628 A B g f s b t a x)). Qed.
Lemma lem5078631 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term383 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5078632 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (a : A) (g : B -> A) (f : A -> B) (x : A) : term447 A B s t b a g f x.
Proof. exact (@lem5078631 (term277 A B s t g a b f x) (term444 A B s b t a x) (x = a) (term441 A B s t b a g f x)). Qed.
Lemma lem5078647 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term277 A B s t g a b f x) = (term448 A B s t b a g f x).
Proof. exact (@lem5078632 A B s t b a g f x (@lem5078629 A B g f s b t a x)). Qed.
Lemma lem5078663 {A B : Type'} (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : ((f x) = b) = False.
Proof. exact (h1). Qed.
Lemma lem5078664 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078665 {A B : Type'} (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term436 A B f x b) = (@COND A False).
Proof. exact (MK_COMB (@lem5078664 A) (@lem5078663 A B f x b h1)). Qed.
Lemma lem5078666 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078667 {A B : Type'} (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term437 A B f x b a) = (@COND A False a).
Proof. exact (MK_COMB (@lem5078665 A B f x b h1) (@lem5078666 A a)). Qed.
Lemma lem5078668 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term100 A B g f x) = (term100 A B g f x).
Proof. exact (eq_refl (term100 A B g f x)). Qed.
Lemma lem5078669 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term438 A B b a g f x) = (term449 A B a g f x).
Proof. exact (MK_COMB (@lem5078667 A B a f x b h1) (@lem5078668 A B g f x)). Qed.
Lemma lem5078671 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5078672 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem5078671 A t1 t2). Qed.
Lemma lem5078673 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (x : A) : (term449 A B a g f x) = (term100 A B g f x).
Proof. exact (@lem5078672 A a (term100 A B g f x)). Qed.
Lemma lem5078674 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term438 A B b a g f x) = (term100 A B g f x).
Proof. exact (TRANS (@lem5078669 A B a g f x b h1) (@lem5078673 A B a g f x)). Qed.
Lemma lem5078675 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5078676 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term439 A B b a g f x) = (term450 A B g f x).
Proof. exact (MK_COMB (@lem5078675 A) (@lem5078674 A B a g f x b h1)). Qed.
Lemma lem5078677 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5078678 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : ((term438 A B b a g f x) = x) = ((term100 A B g f x) = x).
Proof. exact (MK_COMB (@lem5078676 A B a g f x b h1) (@lem5078677 A x)). Qed.
Lemma lem5078681 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term435 A B f x t) = (term435 A B f x t).
Proof. exact (eq_refl (term435 A B f x t)). Qed.
Lemma lem5078682 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term440 A B t b a g f x) = (term451 A B t g f x).
Proof. exact (MK_COMB (@lem5078681 A B f x t) (@lem5078678 A B a g f x b h1)). Qed.
Lemma lem5078685 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (term205 A x s).
Proof. exact (eq_refl (term205 A x s)). Qed.
Lemma lem5078686 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term441 A B s t b a g f x) = (term452 A B s t g f x).
Proof. exact (MK_COMB (@lem5078685 A x s) (@lem5078682 A B a t g f x b h1)). Qed.
Lemma lem5078689 {A : Type'} (x : A) (a : A) : (term413 A x a) = (term413 A x a).
Proof. exact (eq_refl (term413 A x a)). Qed.
Lemma lem5078690 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term453 A B s t b a g f x) = (term454 A B a s t g f x).
Proof. exact (MK_COMB (@lem5078689 A x a) (@lem5078686 A B a s t g f x b h1)). Qed.
Lemma lem5078693 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term455 A B s b t a x) = (term455 A B s b t a x).
Proof. exact (eq_refl (term455 A B s b t a x)). Qed.
Lemma lem5078694 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = False) : (term448 A B s t b a g f x) = (term456 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5078693 A B s b t a x) (@lem5078690 A B a s t g f x b h1)). Qed.
Lemma lem5078697 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : term457 A B b a s t g f x.
Proof. exact (fun h0 : ((f x) = b) = False => @lem5078694 A B a s t g f x b h0). Qed.
Lemma lem5078711 {A B : Type'} (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : ((f x) = b) = True.
Proof. exact (h1). Qed.
Lemma lem5078712 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem5078713 {A B : Type'} (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term436 A B f x b) = (@COND A True).
Proof. exact (MK_COMB (@lem5078712 A) (@lem5078711 A B f x b h1)). Qed.
Lemma lem5078714 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5078715 {A B : Type'} (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term437 A B f x b a) = (@COND A True a).
Proof. exact (MK_COMB (@lem5078713 A B f x b h1) (@lem5078714 A a)). Qed.
Lemma lem5078716 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term100 A B g f x) = (term100 A B g f x).
Proof. exact (eq_refl (term100 A B g f x)). Qed.
Lemma lem5078717 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term438 A B b a g f x) = (term458 A B a g f x).
Proof. exact (MK_COMB (@lem5078715 A B a f x b h1) (@lem5078716 A B g f x)). Qed.
Lemma lem5078719 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5078720 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem5078719 A t2 t1). Qed.
Lemma lem5078721 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (a : A) : (term458 A B a g f x) = a.
Proof. exact (@lem5078720 A (term100 A B g f x) a). Qed.
Lemma lem5078722 {A B : Type'} (g : B -> A) (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term438 A B b a g f x) = a.
Proof. exact (TRANS (@lem5078717 A B a g f x b h1) (@lem5078721 A B g f x a)). Qed.
Lemma lem5078723 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5078724 {A B : Type'} (g : B -> A) (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term439 A B b a g f x) = (@eq A a).
Proof. exact (MK_COMB (@lem5078723 A) (@lem5078722 A B g a f x b h1)). Qed.
Lemma lem5078725 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5078726 {A B : Type'} (g : B -> A) (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : ((term438 A B b a g f x) = x) = (a = x).
Proof. exact (MK_COMB (@lem5078724 A B g a f x b h1) (@lem5078725 A x)). Qed.
Lemma lem5078729 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term435 A B f x t) = (term435 A B f x t).
Proof. exact (eq_refl (term435 A B f x t)). Qed.
Lemma lem5078730 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term440 A B t b a g f x) = (term459 A B f t a x).
Proof. exact (MK_COMB (@lem5078729 A B f x t) (@lem5078726 A B g a f x b h1)). Qed.
Lemma lem5078733 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (term205 A x s).
Proof. exact (eq_refl (term205 A x s)). Qed.
Lemma lem5078734 {A B : Type'} (g : B -> A) (s : A -> Prop) (t : B -> Prop) (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term441 A B s t b a g f x) = (term460 A B s f t a x).
Proof. exact (MK_COMB (@lem5078733 A x s) (@lem5078730 A B g t a f x b h1)). Qed.
Lemma lem5078737 {A : Type'} (x : A) (a : A) : (term413 A x a) = (term413 A x a).
Proof. exact (eq_refl (term413 A x a)). Qed.
Lemma lem5078738 {A B : Type'} (g : B -> A) (s : A -> Prop) (t : B -> Prop) (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term453 A B s t b a g f x) = (term461 A B s f t a x).
Proof. exact (MK_COMB (@lem5078737 A x a) (@lem5078734 A B g s t a f x b h1)). Qed.
Lemma lem5078741 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term455 A B s b t a x) = (term455 A B s b t a x).
Proof. exact (eq_refl (term455 A B s b t a x)). Qed.
Lemma lem5078742 {A B : Type'} (g : B -> A) (s : A -> Prop) (t : B -> Prop) (a : A) (f : A -> B) (x : A) (b : B) (h1 : ((f x) = b) = True) : (term448 A B s t b a g f x) = (term462 A B b s f t a x).
Proof. exact (MK_COMB (@lem5078741 A B s b t a x) (@lem5078738 A B g s t a f x b h1)). Qed.
Lemma lem5078745 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : term463 A B g b s f t a x.
Proof. exact (fun h0 : ((f x) = b) = True => @lem5078742 A B g s t a f x b h0). Qed.
Lemma lem5078746 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : term464 A B g b s f t a x.
Proof. exact (conj (@lem5078697 A B b a s t g f x) (@lem5078745 A B g b s f t a x)). Qed.
Lemma lem5078748 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term383 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem5078749 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : term465 A B b a s t g f x.
Proof. exact (@lem5078748 (term448 A B s t b a g f x) (term462 A B b s f t a x) ((f x) = b) (term456 A B b a s t g f x)). Qed.
Lemma lem5078842 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term448 A B s t b a g f x) = (term466 A B b a s t g f x).
Proof. exact (@lem5078749 A B b a s t g f x (@lem5078746 A B g b s f t a x)). Qed.
Lemma lem5078843 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (a : A) (b : B) (f : A -> B) (x : A) : (term467 A B s t g a b f x) = (term467 A B s t g a b f x).
Proof. exact (eq_refl (term467 A B s t g a b f x)). Qed.
Lemma lem5078844 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : ((term277 A B s t g a b f x) = (term448 A B s t b a g f x)) = ((term277 A B s t g a b f x) = (term466 A B b a s t g f x)).
Proof. exact (MK_COMB (@lem5078843 A B s t g a b f x) (@lem5078842 A B b a s t g f x)). Qed.
Lemma lem5078845 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term277 A B s t g a b f x) = (term466 A B b a s t g f x).
Proof. exact (EQ_MP (@lem5078844 A B b a s t g f x) (@lem5078647 A B s t b a g f x)). Qed.
Lemma lem5078846 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term279 A B s t g a b f) = (term468 A B b a s t g f).
Proof. exact (fun_ext (fun x : A => @lem5078845 A B b a s t g f x)). Qed.
Lemma lem5078847 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5078848 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term281 A B s t g a b f) = (term469 A B b a s t g f).
Proof. exact (MK_COMB (@lem5078847 A) (@lem5078846 A B b a s t g f)). Qed.
Lemma lem5078849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5078850 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term283 A B s t g a b f) = (term470 A B b a s t g f).
Proof. exact (MK_COMB (@lem5078849) (@lem5078848 A B b a s t g f)). Qed.
Lemma lem5078851 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term314 A B t s f b a g) = (term471 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078850 A B b a s t g f) (@lem5078472 A B a b t s f g)). Qed.
Lemma lem5078872 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term129 A B t b s a f g y) = (term129 A B t b s a f g y).
Proof. exact (eq_refl (term129 A B t b s a f g y)). Qed.
Lemma lem5078873 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term131 A B t b s a f g) = (term131 A B t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5078872 A B t b s a f g y)). Qed.
Lemma lem5078874 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5078875 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term133 A B t b s a f g) = (term133 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078874 B) (@lem5078873 A B t b s a f g)). Qed.
Lemma lem5078876 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5078877 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term199 A B t b s a f g) = (term199 A B t b s a f g).
Proof. exact (MK_COMB (@lem5078876) (@lem5078875 A B t b s a f g)). Qed.
Lemma lem5078878 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term366 A B t s f b a g) = (term472 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078877 A B t b s a f g) (@lem5078851 A B a b t s f g)). Qed.
Lemma lem5078899 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term105 A B s a t b g f x) = (term105 A B s a t b g f x).
Proof. exact (eq_refl (term105 A B s a t b g f x)). Qed.
Lemma lem5078900 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term107 A B s a t b g f) = (term107 A B s a t b g f).
Proof. exact (fun_ext (fun x : A => @lem5078899 A B s a t b g f x)). Qed.
Lemma lem5078901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5078902 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term109 A B s a t b g f) = (term109 A B s a t b g f).
Proof. exact (MK_COMB (@lem5078901 A) (@lem5078900 A B s a t b g f)). Qed.
Lemma lem5078903 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5078904 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term202 A B s a t b g f) = (term202 A B s a t b g f).
Proof. exact (MK_COMB (@lem5078903) (@lem5078902 A B s a t b g f)). Qed.
Lemma lem5078905 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term367 A B t s f b a g) = (term473 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078904 A B s a t b g f) (@lem5078878 A B a b t s f g)). Qed.
Lemma lem5078908 {B : Type'} (b : B) (t : B -> Prop) : (term205 B b t) = (term205 B b t).
Proof. exact (eq_refl (term205 B b t)). Qed.
Lemma lem5078909 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term368 A B t s f b a g) = (term474 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078908 B b t) (@lem5078905 A B a b t s f g)). Qed.
Lemma lem5078912 {A : Type'} (a : A) (s : A -> Prop) : (term205 A a s) = (term205 A a s).
Proof. exact (eq_refl (term205 A a s)). Qed.
Lemma lem5078913 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term369 A B t s f b a g) = (term475 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078912 A a s) (@lem5078909 A B a b t s f g)). Qed.
Lemma lem5078916 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term210 A B s t) = (term210 A B s t).
Proof. exact (eq_refl (term210 A B s t)). Qed.
Lemma lem5078917 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term370 A B t s f b a g) = (term476 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078916 A B s t) (@lem5078913 A B a b t s f g)). Qed.
Lemma lem5078920 {B : Type'} (t : B -> Prop) : (term213 B t) = (term213 B t).
Proof. exact (eq_refl (term213 B t)). Qed.
Lemma lem5078921 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term371 A B t s f b a g) = (term477 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078920 B t) (@lem5078917 A B a b t s f g)). Qed.
Lemma lem5078924 {A : Type'} (s : A -> Prop) : (term213 A s) = (term213 A s).
Proof. exact (eq_refl (term213 A s)). Qed.
Lemma lem5078925 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term372 A B t s f b a g) = (term478 A B a b t s f g).
Proof. exact (MK_COMB (@lem5078924 A s) (@lem5078921 A B a b t s f g)). Qed.
Lemma lem5078926 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term373 A B s f b a g) = (term479 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5078925 A B a b t s f g)). Qed.
Lemma lem5078927 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5078928 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term374 A B s f b a g) = (term480 A B a b s f g).
Proof. exact (MK_COMB (@lem5078927 B) (@lem5078926 A B a b s f g)). Qed.
Lemma lem5078929 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term375 A B f b a g) = (term481 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5078928 A B a b s f g)). Qed.
Lemma lem5078930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5078931 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term376 A B f b a g) = (term482 A B a b f g).
Proof. exact (MK_COMB (@lem5078930 A) (@lem5078929 A B a b f g)). Qed.
Lemma lem5078932 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term377 A B b a g) = (term483 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5078931 A B a b f g)). Qed.
Lemma lem5078933 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5078934 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term378 A B b a g) = (term484 A B a b g).
Proof. exact (MK_COMB (@lem5078933 A B) (@lem5078932 A B a b g)). Qed.
Lemma lem5078935 {A B : Type'} (a : A) (g : B -> A) : (term379 A B a g) = (term485 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5078934 A B a b g)). Qed.
Lemma lem5078936 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5078937 {A B : Type'} (a : A) (g : B -> A) : (term380 A B a g) = (term486 A B a g).
Proof. exact (MK_COMB (@lem5078936 B) (@lem5078935 A B a g)). Qed.
Lemma lem5078942 {A : Type'} (a : A) : (term487 A a) = (term487 A a).
Proof. exact (eq_refl (term487 A a)). Qed.
Lemma lem5078943 {A B : Type'} (a : A) (g : B -> A) : (term488 A B a g) = (term489 A B a g).
Proof. exact (MK_COMB (@lem5078942 A a) (@lem5078937 A B a g)). Qed.
Lemma lem5078944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5078945 {A B : Type'} (a : A) (g : B -> A) : (term490 A B a g) = (term491 A B a g).
Proof. exact (MK_COMB (@lem5078944) (@lem5078943 A B a g)). Qed.
Lemma lem5078946 {A B : Type'} (a : A) (g : B -> A) : (term385 A B a g) = (term492 A B a g).
Proof. exact (MK_COMB (@lem5078945 A B a g) (@lem5078096 A B a g)). Qed.
Lemma lem5078947 {A B : Type'} (a : A) (g : B -> A) : (term493 A B a g) = (term493 A B a g).
Proof. exact (eq_refl (term493 A B a g)). Qed.
Lemma lem5078948 {A B : Type'} (a : A) (g : B -> A) : ((term332 A B a g) = (term385 A B a g)) = ((term332 A B a g) = (term492 A B a g)).
Proof. exact (MK_COMB (@lem5078947 A B a g) (@lem5078946 A B a g)). Qed.
Lemma lem5078949 {A B : Type'} (a : A) (g : B -> A) : (term332 A B a g) = (term492 A B a g).
Proof. exact (EQ_MP (@lem5078948 A B a g) (@lem5078007 A B a g)). Qed.
Lemma lem5078950 {A B : Type'} (g : B -> A) : (term333 A B g) = (term494 A B g).
Proof. exact (fun_ext (fun a : A => @lem5078949 A B a g)). Qed.
Lemma lem5078951 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5078952 {A B : Type'} (g : B -> A) : (term334 A B g) = (term495 A B g).
Proof. exact (MK_COMB (@lem5078951 A) (@lem5078950 A B g)). Qed.
Lemma lem5078953 {A B : Type'} : (term335 A B) = (term496 A B).
Proof. exact (fun_ext (fun g : B -> A => @lem5078952 A B g)). Qed.
Lemma lem5078954 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5078955 {A B : Type'} : (term336 A B) = (term497 A B).
Proof. exact (MK_COMB (@lem5078954 A B) (@lem5078953 A B)). Qed.
Lemma lem5079188 {A B : Type'} : (term239 A B) = (term497 A B).
Proof. exact (TRANS (@lem5077563 A B) (@lem5078955 A B)). Qed.
Lemma lem5079189 {A B : Type'} : (term497 A B) = (term239 A B).
Proof. exact (SYM (@lem5079188 A B)). Qed.
Lemma lem5079191 (p : Prop) : p = (term189 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5079192 {A B : Type'} (a : A) (g : B -> A) : (term492 A B a g) = (term498 A B a g).
Proof. exact (@lem5079191 (term492 A B a g)). Qed.
Lemma lem5079193 {A B : Type'} (a : A) (g : B -> A) : (term498 A B a g) = (term492 A B a g).
Proof. exact (SYM (@lem5079192 A B a g)). Qed.
Lemma lem5079194 {A B : Type'} (a : A) (g : B -> A) (h1 : term499 A B a g) : term499 A B a g.
Proof. exact (h1). Qed.
Lemma lem5079197 {A : Type'} (a : A) : (term500 A a) = (a = a).
Proof. exact (@lem16933 (a = a)). Qed.
Lemma lem5079206 {A : Type'} (x : A) (a : A) : (term501 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem5079208 {A : Type'} (x : A) (s : A -> Prop) : (term502 A x s) = (term502 A x s).
Proof. exact (eq_refl (term502 A x s)). Qed.
Lemma lem5079209 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term503 A s x a) = (term504 A s x a).
Proof. exact (MK_COMB (@lem5079208 A x s) (@lem5079206 A x a)). Qed.
Lemma lem5079210 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term505 A s x a) = (term503 A s x a).
Proof. exact (@lem17045 (@IN A x s) (term506 A x a)). Qed.
Lemma lem5079211 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term505 A s x a) = (term504 A s x a).
Proof. exact (TRANS (@lem5079210 A s x a) (@lem5079209 A s x a)). Qed.
Lemma lem5079220 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term101 A B t b g f x) = (term101 A B t b g f x).
Proof. exact (eq_refl (term101 A B t b g f x)). Qed.
Lemma lem5079221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079222 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term507 A s x a) = (term508 A s x a).
Proof. exact (MK_COMB (@lem5079221) (@lem5079211 A s x a)). Qed.
Lemma lem5079223 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term509 A B s a t b g f x) = (term510 A B s a t b g f x).
Proof. exact (MK_COMB (@lem5079222 A s x a) (@lem5079220 A B t b g f x)). Qed.
Lemma lem5079224 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term105 A B s a t b g f x) = (term509 A B s a t b g f x).
Proof. exact (@lem17265 (term27 A s x a) (term101 A B t b g f x)). Qed.
Lemma lem5079225 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term105 A B s a t b g f x) = (term510 A B s a t b g f x).
Proof. exact (TRANS (@lem5079224 A B s a t b g f x) (@lem5079223 A B s a t b g f x)). Qed.
Lemma lem5079226 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term107 A B s a t b g f) = (term511 A B s a t b g f).
Proof. exact (fun_ext (fun x : A => @lem5079225 A B s a t b g f x)). Qed.
Lemma lem5079227 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5079228 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term109 A B s a t b g f) = (term512 A B s a t b g f).
Proof. exact (MK_COMB (@lem5079227 A) (@lem5079226 A B s a t b g f)). Qed.
Lemma lem5079232 {B : Type'} (y : B) (b : B) : (term501 B y b) = (y = b).
Proof. exact (@lem16933 (y = b)). Qed.
Lemma lem5079234 {B : Type'} (y : B) (t : B -> Prop) : (term502 B y t) = (term502 B y t).
Proof. exact (eq_refl (term502 B y t)). Qed.
Lemma lem5079235 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term503 B t y b) = (term504 B t y b).
Proof. exact (MK_COMB (@lem5079234 B y t) (@lem5079232 B y b)). Qed.
Lemma lem5079236 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term505 B t y b) = (term503 B t y b).
Proof. exact (@lem17045 (@IN B y t) (term506 B y b)). Qed.
Lemma lem5079237 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term505 B t y b) = (term504 B t y b).
Proof. exact (TRANS (@lem5079236 B t y b) (@lem5079235 B t y b)). Qed.
Lemma lem5079246 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term125 A B s a f g y) = (term125 A B s a f g y).
Proof. exact (eq_refl (term125 A B s a f g y)). Qed.
Lemma lem5079247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079248 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term507 B t y b) = (term508 B t y b).
Proof. exact (MK_COMB (@lem5079247) (@lem5079237 B t y b)). Qed.
Lemma lem5079249 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term513 A B t b s a f g y) = (term514 A B t b s a f g y).
Proof. exact (MK_COMB (@lem5079248 B t y b) (@lem5079246 A B s a f g y)). Qed.
Lemma lem5079250 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term129 A B t b s a f g y) = (term513 A B t b s a f g y).
Proof. exact (@lem17265 (term27 B t y b) (term125 A B s a f g y)). Qed.
Lemma lem5079251 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term129 A B t b s a f g y) = (term514 A B t b s a f g y).
Proof. exact (TRANS (@lem5079250 A B t b s a f g y) (@lem5079249 A B t b s a f g y)). Qed.
Lemma lem5079252 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term131 A B t b s a f g) = (term515 A B t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5079251 A B t b s a f g y)). Qed.
Lemma lem5079253 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5079254 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term133 A B t b s a f g) = (term516 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079253 B) (@lem5079252 A B t b s a f g)). Qed.
Lemma lem5079257 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term517 A B f x b) = ((f x) = b).
Proof. exact (@lem16933 ((f x) = b)). Qed.
Lemma lem5079260 {A : Type'} (x : A) (a : A) : (term501 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem5079268 {A B : Type'} (b : B) (t : B -> Prop) (a : A) (x : A) : (term518 A B b t a x) = (term519 A B b t a x).
Proof. exact (@lem17045 (@IN B b t) (a = x)). Qed.
Lemma lem5079270 {A : Type'} (x : A) (s : A -> Prop) : (term402 A x s) = (term402 A x s).
Proof. exact (eq_refl (term402 A x s)). Qed.
Lemma lem5079271 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term520 A B s b t a x) = (term521 A B s b t a x).
Proof. exact (MK_COMB (@lem5079270 A x s) (@lem5079268 A B b t a x)). Qed.
Lemma lem5079272 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term522 A B s b t a x) = (term520 A B s b t a x).
Proof. exact (@lem17362 (@IN A x s) (term443 A B b t a x)). Qed.
Lemma lem5079273 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term522 A B s b t a x) = (term521 A B s b t a x).
Proof. exact (TRANS (@lem5079272 A B s b t a x) (@lem5079271 A B s b t a x)). Qed.
Lemma lem5079274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079275 {A : Type'} (x : A) (a : A) : (term523 A x a) = (term524 A x a).
Proof. exact (MK_COMB (@lem5079274) (@lem5079260 A x a)). Qed.
Lemma lem5079276 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term525 A B s b t a x) = (term526 A B s b t a x).
Proof. exact (MK_COMB (@lem5079275 A x a) (@lem5079273 A B s b t a x)). Qed.
Lemma lem5079277 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term527 A B s b t a x) = (term525 A B s b t a x).
Proof. exact (@lem17160 (term506 A x a) (term444 A B s b t a x)). Qed.
Lemma lem5079278 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term527 A B s b t a x) = (term526 A B s b t a x).
Proof. exact (TRANS (@lem5079277 A B s b t a x) (@lem5079276 A B s b t a x)). Qed.
Lemma lem5079287 {A B : Type'} (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term528 A B f t a x) = (term529 A B f t a x).
Proof. exact (@lem17045 (term434 A B f x t) (a = x)). Qed.
Lemma lem5079289 {A : Type'} (x : A) (s : A -> Prop) : (term402 A x s) = (term402 A x s).
Proof. exact (eq_refl (term402 A x s)). Qed.
Lemma lem5079290 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term530 A B s f t a x) = (term531 A B s f t a x).
Proof. exact (MK_COMB (@lem5079289 A x s) (@lem5079287 A B f t a x)). Qed.
Lemma lem5079291 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term532 A B s f t a x) = (term530 A B s f t a x).
Proof. exact (@lem17362 (@IN A x s) (term459 A B f t a x)). Qed.
Lemma lem5079292 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term532 A B s f t a x) = (term531 A B s f t a x).
Proof. exact (TRANS (@lem5079291 A B s f t a x) (@lem5079290 A B s f t a x)). Qed.
Lemma lem5079294 {A : Type'} (x : A) (a : A) : (term533 A x a) = (term533 A x a).
Proof. exact (eq_refl (term533 A x a)). Qed.
Lemma lem5079295 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term534 A B s f t a x) = (term535 A B s f t a x).
Proof. exact (MK_COMB (@lem5079294 A x a) (@lem5079292 A B s f t a x)). Qed.
Lemma lem5079296 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term536 A B s f t a x) = (term534 A B s f t a x).
Proof. exact (@lem17160 (x = a) (term460 A B s f t a x)). Qed.
Lemma lem5079297 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term536 A B s f t a x) = (term535 A B s f t a x).
Proof. exact (TRANS (@lem5079296 A B s f t a x) (@lem5079295 A B s f t a x)). Qed.
Lemma lem5079298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079299 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term537 A B s b t a x) = (term538 A B s b t a x).
Proof. exact (MK_COMB (@lem5079298) (@lem5079278 A B s b t a x)). Qed.
Lemma lem5079300 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term539 A B b s f t a x) = (term540 A B b s f t a x).
Proof. exact (MK_COMB (@lem5079299 A B s b t a x) (@lem5079297 A B s f t a x)). Qed.
Lemma lem5079301 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term541 A B b s f t a x) = (term539 A B b s f t a x).
Proof. exact (@lem17045 (term542 A B s b t a x) (term461 A B s f t a x)). Qed.
Lemma lem5079302 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term541 A B b s f t a x) = (term540 A B b s f t a x).
Proof. exact (TRANS (@lem5079301 A B b s f t a x) (@lem5079300 A B b s f t a x)). Qed.
Lemma lem5079303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079304 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term543 A B f x b) = (term341 A B f x b).
Proof. exact (MK_COMB (@lem5079303) (@lem5079257 A B f x b)). Qed.
Lemma lem5079305 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term544 A B b s f t a x) = (term545 A B b s f t a x).
Proof. exact (MK_COMB (@lem5079304 A B f x b) (@lem5079302 A B b s f t a x)). Qed.
Lemma lem5079306 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term546 A B b s f t a x) = (term544 A B b s f t a x).
Proof. exact (@lem17160 (term547 A B f x b) (term462 A B b s f t a x)). Qed.
Lemma lem5079307 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term546 A B b s f t a x) = (term545 A B b s f t a x).
Proof. exact (TRANS (@lem5079306 A B b s f t a x) (@lem5079305 A B b s f t a x)). Qed.
Lemma lem5079311 {A : Type'} (x : A) (a : A) : (term501 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem5079319 {A B : Type'} (b : B) (t : B -> Prop) (a : A) (x : A) : (term518 A B b t a x) = (term519 A B b t a x).
Proof. exact (@lem17045 (@IN B b t) (a = x)). Qed.
Lemma lem5079321 {A : Type'} (x : A) (s : A -> Prop) : (term402 A x s) = (term402 A x s).
Proof. exact (eq_refl (term402 A x s)). Qed.
Lemma lem5079322 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term520 A B s b t a x) = (term521 A B s b t a x).
Proof. exact (MK_COMB (@lem5079321 A x s) (@lem5079319 A B b t a x)). Qed.
Lemma lem5079323 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term522 A B s b t a x) = (term520 A B s b t a x).
Proof. exact (@lem17362 (@IN A x s) (term443 A B b t a x)). Qed.
Lemma lem5079324 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term522 A B s b t a x) = (term521 A B s b t a x).
Proof. exact (TRANS (@lem5079323 A B s b t a x) (@lem5079322 A B s b t a x)). Qed.
Lemma lem5079325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079326 {A : Type'} (x : A) (a : A) : (term523 A x a) = (term524 A x a).
Proof. exact (MK_COMB (@lem5079325) (@lem5079311 A x a)). Qed.
Lemma lem5079327 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term525 A B s b t a x) = (term526 A B s b t a x).
Proof. exact (MK_COMB (@lem5079326 A x a) (@lem5079324 A B s b t a x)). Qed.
Lemma lem5079328 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term527 A B s b t a x) = (term525 A B s b t a x).
Proof. exact (@lem17160 (term506 A x a) (term444 A B s b t a x)). Qed.
Lemma lem5079329 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term527 A B s b t a x) = (term526 A B s b t a x).
Proof. exact (TRANS (@lem5079328 A B s b t a x) (@lem5079327 A B s b t a x)). Qed.
Lemma lem5079338 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term548 A B t g f x) = (term549 A B t g f x).
Proof. exact (@lem17045 (term434 A B f x t) ((term100 A B g f x) = x)). Qed.
Lemma lem5079340 {A : Type'} (x : A) (s : A -> Prop) : (term402 A x s) = (term402 A x s).
Proof. exact (eq_refl (term402 A x s)). Qed.
Lemma lem5079341 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term550 A B s t g f x) = (term551 A B s t g f x).
Proof. exact (MK_COMB (@lem5079340 A x s) (@lem5079338 A B t g f x)). Qed.
Lemma lem5079342 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term552 A B s t g f x) = (term550 A B s t g f x).
Proof. exact (@lem17362 (@IN A x s) (term451 A B t g f x)). Qed.
Lemma lem5079343 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term552 A B s t g f x) = (term551 A B s t g f x).
Proof. exact (TRANS (@lem5079342 A B s t g f x) (@lem5079341 A B s t g f x)). Qed.
Lemma lem5079345 {A : Type'} (x : A) (a : A) : (term533 A x a) = (term533 A x a).
Proof. exact (eq_refl (term533 A x a)). Qed.
Lemma lem5079346 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term553 A B a s t g f x) = (term554 A B a s t g f x).
Proof. exact (MK_COMB (@lem5079345 A x a) (@lem5079343 A B s t g f x)). Qed.
Lemma lem5079347 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term555 A B a s t g f x) = (term553 A B a s t g f x).
Proof. exact (@lem17160 (x = a) (term452 A B s t g f x)). Qed.
Lemma lem5079348 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term555 A B a s t g f x) = (term554 A B a s t g f x).
Proof. exact (TRANS (@lem5079347 A B a s t g f x) (@lem5079346 A B a s t g f x)). Qed.
Lemma lem5079349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079350 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) : (term537 A B s b t a x) = (term538 A B s b t a x).
Proof. exact (MK_COMB (@lem5079349) (@lem5079329 A B s b t a x)). Qed.
Lemma lem5079351 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term556 A B b a s t g f x) = (term557 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5079350 A B s b t a x) (@lem5079348 A B a s t g f x)). Qed.
Lemma lem5079352 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term558 A B b a s t g f x) = (term556 A B b a s t g f x).
Proof. exact (@lem17045 (term542 A B s b t a x) (term454 A B a s t g f x)). Qed.
Lemma lem5079353 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term558 A B b a s t g f x) = (term557 A B b a s t g f x).
Proof. exact (TRANS (@lem5079352 A B b a s t g f x) (@lem5079351 A B b a s t g f x)). Qed.
Lemma lem5079355 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term559 A B f x b) = (term559 A B f x b).
Proof. exact (eq_refl (term559 A B f x b)). Qed.
Lemma lem5079356 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term560 A B b a s t g f x) = (term561 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5079355 A B f x b) (@lem5079353 A B b a s t g f x)). Qed.
Lemma lem5079357 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term562 A B b a s t g f x) = (term560 A B b a s t g f x).
Proof. exact (@lem17160 ((f x) = b) (term456 A B b a s t g f x)). Qed.
Lemma lem5079358 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term562 A B b a s t g f x) = (term561 A B b a s t g f x).
Proof. exact (TRANS (@lem5079357 A B b a s t g f x) (@lem5079356 A B b a s t g f x)). Qed.
Lemma lem5079359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079360 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term563 A B b s f t a x) = (term564 A B b s f t a x).
Proof. exact (MK_COMB (@lem5079359) (@lem5079307 A B b s f t a x)). Qed.
Lemma lem5079361 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term565 A B b a s t g f x) = (term566 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5079360 A B b s f t a x) (@lem5079358 A B b a s t g f x)). Qed.
Lemma lem5079362 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term567 A B b a s t g f x) = (term565 A B b a s t g f x).
Proof. exact (@lem17045 (term568 A B b s f t a x) (term569 A B b a s t g f x)). Qed.
Lemma lem5079363 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term567 A B b a s t g f x) = (term566 A B b a s t g f x).
Proof. exact (TRANS (@lem5079362 A B b a s t g f x) (@lem5079361 A B b a s t g f x)). Qed.
Lemma lem5079364 {A : Type'} (P : A -> Prop) : (term570 A P) = (term571 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5079365 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term572 A B b a s t g f) = (term573 A B b a s t g f).
Proof. exact (@lem5079364 A (term468 A B b a s t g f)). Qed.
Lemma lem5079366 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term574 A B b a s t g f x) = (term466 A B b a s t g f x).
Proof. exact (eq_refl (term574 A B b a s t g f x)). Qed.
Lemma lem5079367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079368 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term575 A B b a s t g f x) = (term567 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5079367) (@lem5079366 A B b a s t g f x)). Qed.
Lemma lem5079369 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term575 A B b a s t g f x) = (term566 A B b a s t g f x).
Proof. exact (TRANS (@lem5079368 A B b a s t g f x) (@lem5079363 A B b a s t g f x)). Qed.
Lemma lem5079370 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term576 A B b a s t g f) = (term577 A B b a s t g f).
Proof. exact (fun_ext (fun x : A => @lem5079369 A B b a s t g f x)). Qed.
Lemma lem5079371 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5079372 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term573 A B b a s t g f) = (term578 A B b a s t g f).
Proof. exact (MK_COMB (@lem5079371 A) (@lem5079370 A B b a s t g f)). Qed.
Lemma lem5079373 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term572 A B b a s t g f) = (term578 A B b a s t g f).
Proof. exact (TRANS (@lem5079365 A B b a s t g f) (@lem5079372 A B b a s t g f)). Qed.
Lemma lem5079376 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term579 A B g y a) = ((g y) = a).
Proof. exact (@lem16933 ((g y) = a)). Qed.
Lemma lem5079379 {B : Type'} (y : B) (b : B) : (term501 B y b) = (y = b).
Proof. exact (@lem16933 (y = b)). Qed.
Lemma lem5079387 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (y : B) : (term580 A B a s b y) = (term581 A B a s b y).
Proof. exact (@lem17045 (@IN A a s) (b = y)). Qed.
Lemma lem5079389 {B : Type'} (y : B) (t : B -> Prop) : (term402 B y t) = (term402 B y t).
Proof. exact (eq_refl (term402 B y t)). Qed.
Lemma lem5079390 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term582 A B t a s b y) = (term583 A B t a s b y).
Proof. exact (MK_COMB (@lem5079389 B y t) (@lem5079387 A B a s b y)). Qed.
Lemma lem5079391 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term584 A B t a s b y) = (term582 A B t a s b y).
Proof. exact (@lem17362 (@IN B y t) (term403 A B a s b y)). Qed.
Lemma lem5079392 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term584 A B t a s b y) = (term583 A B t a s b y).
Proof. exact (TRANS (@lem5079391 A B t a s b y) (@lem5079390 A B t a s b y)). Qed.
Lemma lem5079393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079394 {B : Type'} (y : B) (b : B) : (term523 B y b) = (term524 B y b).
Proof. exact (MK_COMB (@lem5079393) (@lem5079379 B y b)). Qed.
Lemma lem5079395 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term585 A B t a s b y) = (term586 A B t a s b y).
Proof. exact (MK_COMB (@lem5079394 B y b) (@lem5079392 A B t a s b y)). Qed.
Lemma lem5079396 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term587 A B t a s b y) = (term585 A B t a s b y).
Proof. exact (@lem17160 (term506 B y b) (term404 A B t a s b y)). Qed.
Lemma lem5079397 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term587 A B t a s b y) = (term586 A B t a s b y).
Proof. exact (TRANS (@lem5079396 A B t a s b y) (@lem5079395 A B t a s b y)). Qed.
Lemma lem5079406 {A B : Type'} (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term588 A B g s b y) = (term589 A B g s b y).
Proof. exact (@lem17045 (term392 A B g y s) (b = y)). Qed.
Lemma lem5079408 {B : Type'} (y : B) (t : B -> Prop) : (term402 B y t) = (term402 B y t).
Proof. exact (eq_refl (term402 B y t)). Qed.
Lemma lem5079409 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term590 A B t g s b y) = (term591 A B t g s b y).
Proof. exact (MK_COMB (@lem5079408 B y t) (@lem5079406 A B g s b y)). Qed.
Lemma lem5079410 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term592 A B t g s b y) = (term590 A B t g s b y).
Proof. exact (@lem17362 (@IN B y t) (term420 A B g s b y)). Qed.
Lemma lem5079411 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term592 A B t g s b y) = (term591 A B t g s b y).
Proof. exact (TRANS (@lem5079410 A B t g s b y) (@lem5079409 A B t g s b y)). Qed.
Lemma lem5079413 {B : Type'} (y : B) (b : B) : (term533 B y b) = (term533 B y b).
Proof. exact (eq_refl (term533 B y b)). Qed.
Lemma lem5079414 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term593 A B t g s b y) = (term594 A B t g s b y).
Proof. exact (MK_COMB (@lem5079413 B y b) (@lem5079411 A B t g s b y)). Qed.
Lemma lem5079415 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term595 A B t g s b y) = (term593 A B t g s b y).
Proof. exact (@lem17160 (y = b) (term421 A B t g s b y)). Qed.
Lemma lem5079416 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term595 A B t g s b y) = (term594 A B t g s b y).
Proof. exact (TRANS (@lem5079415 A B t g s b y) (@lem5079414 A B t g s b y)). Qed.
Lemma lem5079417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079418 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term596 A B t a s b y) = (term597 A B t a s b y).
Proof. exact (MK_COMB (@lem5079417) (@lem5079397 A B t a s b y)). Qed.
Lemma lem5079419 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term598 A B a t g s b y) = (term599 A B a t g s b y).
Proof. exact (MK_COMB (@lem5079418 A B t a s b y) (@lem5079416 A B t g s b y)). Qed.
Lemma lem5079420 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term600 A B a t g s b y) = (term598 A B a t g s b y).
Proof. exact (@lem17045 (term601 A B t a s b y) (term422 A B t g s b y)). Qed.
Lemma lem5079421 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term600 A B a t g s b y) = (term599 A B a t g s b y).
Proof. exact (TRANS (@lem5079420 A B a t g s b y) (@lem5079419 A B a t g s b y)). Qed.
Lemma lem5079422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079423 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term602 A B g y a) = (term603 A B g y a).
Proof. exact (MK_COMB (@lem5079422) (@lem5079376 A B g y a)). Qed.
Lemma lem5079424 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term604 A B a t g s b y) = (term605 A B a t g s b y).
Proof. exact (MK_COMB (@lem5079423 A B g y a) (@lem5079421 A B a t g s b y)). Qed.
Lemma lem5079425 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term606 A B a t g s b y) = (term604 A B a t g s b y).
Proof. exact (@lem17160 (term607 A B g y a) (term423 A B a t g s b y)). Qed.
Lemma lem5079426 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term606 A B a t g s b y) = (term605 A B a t g s b y).
Proof. exact (TRANS (@lem5079425 A B a t g s b y) (@lem5079424 A B a t g s b y)). Qed.
Lemma lem5079430 {B : Type'} (y : B) (b : B) : (term501 B y b) = (y = b).
Proof. exact (@lem16933 (y = b)). Qed.
Lemma lem5079438 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (y : B) : (term580 A B a s b y) = (term581 A B a s b y).
Proof. exact (@lem17045 (@IN A a s) (b = y)). Qed.
Lemma lem5079440 {B : Type'} (y : B) (t : B -> Prop) : (term402 B y t) = (term402 B y t).
Proof. exact (eq_refl (term402 B y t)). Qed.
Lemma lem5079441 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term582 A B t a s b y) = (term583 A B t a s b y).
Proof. exact (MK_COMB (@lem5079440 B y t) (@lem5079438 A B a s b y)). Qed.
Lemma lem5079442 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term584 A B t a s b y) = (term582 A B t a s b y).
Proof. exact (@lem17362 (@IN B y t) (term403 A B a s b y)). Qed.
Lemma lem5079443 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term584 A B t a s b y) = (term583 A B t a s b y).
Proof. exact (TRANS (@lem5079442 A B t a s b y) (@lem5079441 A B t a s b y)). Qed.
Lemma lem5079444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079445 {B : Type'} (y : B) (b : B) : (term523 B y b) = (term524 B y b).
Proof. exact (MK_COMB (@lem5079444) (@lem5079430 B y b)). Qed.
Lemma lem5079446 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term585 A B t a s b y) = (term586 A B t a s b y).
Proof. exact (MK_COMB (@lem5079445 B y b) (@lem5079443 A B t a s b y)). Qed.
Lemma lem5079447 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term587 A B t a s b y) = (term585 A B t a s b y).
Proof. exact (@lem17160 (term506 B y b) (term404 A B t a s b y)). Qed.
Lemma lem5079448 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term587 A B t a s b y) = (term586 A B t a s b y).
Proof. exact (TRANS (@lem5079447 A B t a s b y) (@lem5079446 A B t a s b y)). Qed.
Lemma lem5079457 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term608 A B s f g y) = (term609 A B s f g y).
Proof. exact (@lem17045 (term392 A B g y s) ((term124 A B f g y) = y)). Qed.
Lemma lem5079459 {B : Type'} (y : B) (t : B -> Prop) : (term402 B y t) = (term402 B y t).
Proof. exact (eq_refl (term402 B y t)). Qed.
Lemma lem5079460 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term610 A B t s f g y) = (term611 A B t s f g y).
Proof. exact (MK_COMB (@lem5079459 B y t) (@lem5079457 A B s f g y)). Qed.
Lemma lem5079461 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term612 A B t s f g y) = (term610 A B t s f g y).
Proof. exact (@lem17362 (@IN B y t) (term411 A B s f g y)). Qed.
Lemma lem5079462 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term612 A B t s f g y) = (term611 A B t s f g y).
Proof. exact (TRANS (@lem5079461 A B t s f g y) (@lem5079460 A B t s f g y)). Qed.
Lemma lem5079464 {B : Type'} (y : B) (b : B) : (term533 B y b) = (term533 B y b).
Proof. exact (eq_refl (term533 B y b)). Qed.
Lemma lem5079465 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term613 A B b t s f g y) = (term614 A B b t s f g y).
Proof. exact (MK_COMB (@lem5079464 B y b) (@lem5079462 A B t s f g y)). Qed.
Lemma lem5079466 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term615 A B b t s f g y) = (term613 A B b t s f g y).
Proof. exact (@lem17160 (y = b) (term412 A B t s f g y)). Qed.
Lemma lem5079467 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term615 A B b t s f g y) = (term614 A B b t s f g y).
Proof. exact (TRANS (@lem5079466 A B b t s f g y) (@lem5079465 A B b t s f g y)). Qed.
Lemma lem5079468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079469 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) : (term596 A B t a s b y) = (term597 A B t a s b y).
Proof. exact (MK_COMB (@lem5079468) (@lem5079448 A B t a s b y)). Qed.
Lemma lem5079470 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term616 A B a b t s f g y) = (term617 A B a b t s f g y).
Proof. exact (MK_COMB (@lem5079469 A B t a s b y) (@lem5079467 A B b t s f g y)). Qed.
Lemma lem5079471 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term618 A B a b t s f g y) = (term616 A B a b t s f g y).
Proof. exact (@lem17045 (term601 A B t a s b y) (term415 A B b t s f g y)). Qed.
Lemma lem5079472 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term618 A B a b t s f g y) = (term617 A B a b t s f g y).
Proof. exact (TRANS (@lem5079471 A B a b t s f g y) (@lem5079470 A B a b t s f g y)). Qed.
Lemma lem5079474 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term619 A B g y a) = (term619 A B g y a).
Proof. exact (eq_refl (term619 A B g y a)). Qed.
Lemma lem5079475 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term620 A B a b t s f g y) = (term621 A B a b t s f g y).
Proof. exact (MK_COMB (@lem5079474 A B g y a) (@lem5079472 A B a b t s f g y)). Qed.
Lemma lem5079476 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term622 A B a b t s f g y) = (term620 A B a b t s f g y).
Proof. exact (@lem17160 ((g y) = a) (term417 A B a b t s f g y)). Qed.
Lemma lem5079477 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term622 A B a b t s f g y) = (term621 A B a b t s f g y).
Proof. exact (TRANS (@lem5079476 A B a b t s f g y) (@lem5079475 A B a b t s f g y)). Qed.
Lemma lem5079478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079479 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term623 A B a t g s b y) = (term624 A B a t g s b y).
Proof. exact (MK_COMB (@lem5079478) (@lem5079426 A B a t g s b y)). Qed.
Lemma lem5079480 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term625 A B a b t s f g y) = (term626 A B a b t s f g y).
Proof. exact (MK_COMB (@lem5079479 A B a t g s b y) (@lem5079477 A B a b t s f g y)). Qed.
Lemma lem5079481 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term627 A B a b t s f g y) = (term625 A B a b t s f g y).
Proof. exact (@lem17045 (term628 A B a t g s b y) (term629 A B a b t s f g y)). Qed.
Lemma lem5079482 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term627 A B a b t s f g y) = (term626 A B a b t s f g y).
Proof. exact (TRANS (@lem5079481 A B a b t s f g y) (@lem5079480 A B a b t s f g y)). Qed.
Lemma lem5079483 {B : Type'} (P : B -> Prop) : (term570 B P) = (term571 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5079484 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term630 A B a b t s f g) = (term631 A B a b t s f g).
Proof. exact (@lem5079483 B (term429 A B a b t s f g)). Qed.
Lemma lem5079485 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term632 A B a b t s f g y) = (term427 A B a b t s f g y).
Proof. exact (eq_refl (term632 A B a b t s f g y)). Qed.
Lemma lem5079486 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079487 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term633 A B a b t s f g y) = (term627 A B a b t s f g y).
Proof. exact (MK_COMB (@lem5079486) (@lem5079485 A B a b t s f g y)). Qed.
Lemma lem5079488 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term633 A B a b t s f g y) = (term626 A B a b t s f g y).
Proof. exact (TRANS (@lem5079487 A B a b t s f g y) (@lem5079482 A B a b t s f g y)). Qed.
Lemma lem5079489 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term634 A B a b t s f g) = (term635 A B a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5079488 A B a b t s f g y)). Qed.
Lemma lem5079490 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5079491 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term631 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079490 B) (@lem5079489 A B a b t s f g)). Qed.
Lemma lem5079492 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term630 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (TRANS (@lem5079484 A B a b t s f g) (@lem5079491 A B a b t s f g)). Qed.
Lemma lem5079493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079494 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term637 A B b a s t g f) = (term638 A B b a s t g f).
Proof. exact (MK_COMB (@lem5079493) (@lem5079373 A B b a s t g f)). Qed.
Lemma lem5079495 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term639 A B a b t s f g) = (term640 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079494 A B b a s t g f) (@lem5079492 A B a b t s f g)). Qed.
Lemma lem5079496 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term641 A B a b t s f g) = (term639 A B a b t s f g).
Proof. exact (@lem17045 (term469 A B b a s t g f) (term430 A B a b t s f g)). Qed.
Lemma lem5079497 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term641 A B a b t s f g) = (term640 A B a b t s f g).
Proof. exact (TRANS (@lem5079496 A B a b t s f g) (@lem5079495 A B a b t s f g)). Qed.
Lemma lem5079498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079499 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term642 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079498) (@lem5079254 A B t b s a f g)). Qed.
Lemma lem5079500 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term644 A B a b t s f g) = (term645 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079499 A B t b s a f g) (@lem5079497 A B a b t s f g)). Qed.
Lemma lem5079501 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term646 A B a b t s f g) = (term644 A B a b t s f g).
Proof. exact (@lem17362 (term133 A B t b s a f g) (term471 A B a b t s f g)). Qed.
Lemma lem5079502 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term646 A B a b t s f g) = (term645 A B a b t s f g).
Proof. exact (TRANS (@lem5079501 A B a b t s f g) (@lem5079500 A B a b t s f g)). Qed.
Lemma lem5079503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079504 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term111 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (MK_COMB (@lem5079503) (@lem5079228 A B s a t b g f)). Qed.
Lemma lem5079505 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term648 A B a b t s f g) = (term649 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079504 A B s a t b g f) (@lem5079502 A B a b t s f g)). Qed.
Lemma lem5079506 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term650 A B a b t s f g) = (term648 A B a b t s f g).
Proof. exact (@lem17362 (term109 A B s a t b g f) (term472 A B a b t s f g)). Qed.
Lemma lem5079507 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term650 A B a b t s f g) = (term649 A B a b t s f g).
Proof. exact (TRANS (@lem5079506 A B a b t s f g) (@lem5079505 A B a b t s f g)). Qed.
Lemma lem5079509 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5079510 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term651 A B a b t s f g) = (term652 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079509 B b t) (@lem5079507 A B a b t s f g)). Qed.
Lemma lem5079511 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term653 A B a b t s f g) = (term651 A B a b t s f g).
Proof. exact (@lem17362 (@IN B b t) (term473 A B a b t s f g)). Qed.
Lemma lem5079512 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term653 A B a b t s f g) = (term652 A B a b t s f g).
Proof. exact (TRANS (@lem5079511 A B a b t s f g) (@lem5079510 A B a b t s f g)). Qed.
Lemma lem5079514 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5079515 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term654 A B a b t s f g) = (term655 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079514 A a s) (@lem5079512 A B a b t s f g)). Qed.
Lemma lem5079516 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term656 A B a b t s f g) = (term654 A B a b t s f g).
Proof. exact (@lem17362 (@IN A a s) (term474 A B a b t s f g)). Qed.
Lemma lem5079517 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term656 A B a b t s f g) = (term655 A B a b t s f g).
Proof. exact (TRANS (@lem5079516 A B a b t s f g) (@lem5079515 A B a b t s f g)). Qed.
Lemma lem5079519 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5079520 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term658 A B a b t s f g) = (term659 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079519 A B s t) (@lem5079517 A B a b t s f g)). Qed.
Lemma lem5079521 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term660 A B a b t s f g) = (term658 A B a b t s f g).
Proof. exact (@lem17362 ((@CARD A s) = (@CARD B t)) (term475 A B a b t s f g)). Qed.
Lemma lem5079522 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term660 A B a b t s f g) = (term659 A B a b t s f g).
Proof. exact (TRANS (@lem5079521 A B a b t s f g) (@lem5079520 A B a b t s f g)). Qed.
Lemma lem5079524 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5079525 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term662 A B a b t s f g) = (term663 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079524 B t) (@lem5079522 A B a b t s f g)). Qed.
Lemma lem5079526 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term664 A B a b t s f g) = (term662 A B a b t s f g).
Proof. exact (@lem17362 (@FINITE B t) (term476 A B a b t s f g)). Qed.
Lemma lem5079527 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term664 A B a b t s f g) = (term663 A B a b t s f g).
Proof. exact (TRANS (@lem5079526 A B a b t s f g) (@lem5079525 A B a b t s f g)). Qed.
Lemma lem5079529 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5079530 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term665 A B a b t s f g) = (term666 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079529 A s) (@lem5079527 A B a b t s f g)). Qed.
Lemma lem5079531 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term667 A B a b t s f g) = (term665 A B a b t s f g).
Proof. exact (@lem17362 (@FINITE A s) (term477 A B a b t s f g)). Qed.
Lemma lem5079532 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term667 A B a b t s f g) = (term666 A B a b t s f g).
Proof. exact (TRANS (@lem5079531 A B a b t s f g) (@lem5079530 A B a b t s f g)). Qed.
Lemma lem5079533 {B : Type'} (P : type686 B) : (term668 B P) = (term669 B P).
Proof. exact (@lem18392 (B -> Prop) P). Qed.
Lemma lem5079534 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term670 A B a b s f g) = (term671 A B a b s f g).
Proof. exact (@lem5079533 B (term479 A B a b s f g)). Qed.
Lemma lem5079535 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term672 A B a b s f g t) = (term478 A B a b t s f g).
Proof. exact (eq_refl (term672 A B a b s f g t)). Qed.
Lemma lem5079536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079537 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term673 A B a b s f g t) = (term667 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079536) (@lem5079535 A B a b t s f g)). Qed.
Lemma lem5079538 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term673 A B a b s f g t) = (term666 A B a b t s f g).
Proof. exact (TRANS (@lem5079537 A B a b t s f g) (@lem5079532 A B a b t s f g)). Qed.
Lemma lem5079539 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term674 A B a b s f g) = (term675 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5079538 A B a b t s f g)). Qed.
Lemma lem5079540 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5079541 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term671 A B a b s f g) = (term676 A B a b s f g).
Proof. exact (MK_COMB (@lem5079540 B) (@lem5079539 A B a b s f g)). Qed.
Lemma lem5079542 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term670 A B a b s f g) = (term676 A B a b s f g).
Proof. exact (TRANS (@lem5079534 A B a b s f g) (@lem5079541 A B a b s f g)). Qed.
Lemma lem5079543 {A : Type'} (P : type686 A) : (term668 A P) = (term669 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem5079544 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term677 A B a b f g) = (term678 A B a b f g).
Proof. exact (@lem5079543 A (term481 A B a b f g)). Qed.
Lemma lem5079545 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term679 A B a b f g s) = (term480 A B a b s f g).
Proof. exact (eq_refl (term679 A B a b f g s)). Qed.
Lemma lem5079546 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079547 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term680 A B a b f g s) = (term670 A B a b s f g).
Proof. exact (MK_COMB (@lem5079546) (@lem5079545 A B a b s f g)). Qed.
Lemma lem5079548 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term680 A B a b f g s) = (term676 A B a b s f g).
Proof. exact (TRANS (@lem5079547 A B a b s f g) (@lem5079542 A B a b s f g)). Qed.
Lemma lem5079549 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term681 A B a b f g) = (term682 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5079548 A B a b s f g)). Qed.
Lemma lem5079550 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5079551 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term678 A B a b f g) = (term683 A B a b f g).
Proof. exact (MK_COMB (@lem5079550 A) (@lem5079549 A B a b f g)). Qed.
Lemma lem5079552 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term677 A B a b f g) = (term683 A B a b f g).
Proof. exact (TRANS (@lem5079544 A B a b f g) (@lem5079551 A B a b f g)). Qed.
Lemma lem5079553 {A B : Type'} (P : type572 A B) : (term684 A B P) = (term685 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem5079554 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term686 A B a b g) = (term687 A B a b g).
Proof. exact (@lem5079553 A B (term483 A B a b g)). Qed.
Lemma lem5079555 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term688 A B a b g f) = (term482 A B a b f g).
Proof. exact (eq_refl (term688 A B a b g f)). Qed.
Lemma lem5079556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079557 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term689 A B a b g f) = (term677 A B a b f g).
Proof. exact (MK_COMB (@lem5079556) (@lem5079555 A B a b f g)). Qed.
Lemma lem5079558 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term689 A B a b g f) = (term683 A B a b f g).
Proof. exact (TRANS (@lem5079557 A B a b f g) (@lem5079552 A B a b f g)). Qed.
Lemma lem5079559 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term690 A B a b g) = (term691 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5079558 A B a b f g)). Qed.
Lemma lem5079560 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5079561 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term687 A B a b g) = (term692 A B a b g).
Proof. exact (MK_COMB (@lem5079560 A B) (@lem5079559 A B a b g)). Qed.
Lemma lem5079562 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term686 A B a b g) = (term692 A B a b g).
Proof. exact (TRANS (@lem5079554 A B a b g) (@lem5079561 A B a b g)). Qed.
Lemma lem5079563 {B : Type'} (P : B -> Prop) : (term570 B P) = (term571 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5079564 {A B : Type'} (a : A) (g : B -> A) : (term693 A B a g) = (term694 A B a g).
Proof. exact (@lem5079563 B (term485 A B a g)). Qed.
Lemma lem5079565 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term695 A B a g b) = (term484 A B a b g).
Proof. exact (eq_refl (term695 A B a g b)). Qed.
Lemma lem5079566 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079567 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term696 A B a g b) = (term686 A B a b g).
Proof. exact (MK_COMB (@lem5079566) (@lem5079565 A B a b g)). Qed.
Lemma lem5079568 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term696 A B a g b) = (term692 A B a b g).
Proof. exact (TRANS (@lem5079567 A B a b g) (@lem5079562 A B a b g)). Qed.
Lemma lem5079569 {A B : Type'} (a : A) (g : B -> A) : (term697 A B a g) = (term698 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5079568 A B a b g)). Qed.
Lemma lem5079570 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5079571 {A B : Type'} (a : A) (g : B -> A) : (term694 A B a g) = (term699 A B a g).
Proof. exact (MK_COMB (@lem5079570 B) (@lem5079569 A B a g)). Qed.
Lemma lem5079572 {A B : Type'} (a : A) (g : B -> A) : (term693 A B a g) = (term699 A B a g).
Proof. exact (TRANS (@lem5079564 A B a g) (@lem5079571 A B a g)). Qed.
Lemma lem5079573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079574 {A : Type'} (a : A) : (term700 A a) = (term701 A a).
Proof. exact (MK_COMB (@lem5079573) (@lem5079197 A a)). Qed.
Lemma lem5079575 {A B : Type'} (a : A) (g : B -> A) : (term702 A B a g) = (term703 A B a g).
Proof. exact (MK_COMB (@lem5079574 A a) (@lem5079572 A B a g)). Qed.
Lemma lem5079576 {A B : Type'} (a : A) (g : B -> A) : (term704 A B a g) = (term702 A B a g).
Proof. exact (@lem17160 (term705 A a) (term486 A B a g)). Qed.
Lemma lem5079577 {A B : Type'} (a : A) (g : B -> A) : (term704 A B a g) = (term703 A B a g).
Proof. exact (TRANS (@lem5079576 A B a g) (@lem5079575 A B a g)). Qed.
Lemma lem5079587 {A : Type'} (x : A) (a : A) : (term501 A x a) = (x = a).
Proof. exact (@lem16933 (x = a)). Qed.
Lemma lem5079589 {A : Type'} (x : A) (s : A -> Prop) : (term502 A x s) = (term502 A x s).
Proof. exact (eq_refl (term502 A x s)). Qed.
Lemma lem5079590 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term503 A s x a) = (term504 A s x a).
Proof. exact (MK_COMB (@lem5079589 A x s) (@lem5079587 A x a)). Qed.
Lemma lem5079591 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term505 A s x a) = (term503 A s x a).
Proof. exact (@lem17045 (@IN A x s) (term506 A x a)). Qed.
Lemma lem5079592 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term505 A s x a) = (term504 A s x a).
Proof. exact (TRANS (@lem5079591 A s x a) (@lem5079590 A s x a)). Qed.
Lemma lem5079601 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term101 A B t b g f x) = (term101 A B t b g f x).
Proof. exact (eq_refl (term101 A B t b g f x)). Qed.
Lemma lem5079602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079603 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term507 A s x a) = (term508 A s x a).
Proof. exact (MK_COMB (@lem5079602) (@lem5079592 A s x a)). Qed.
Lemma lem5079604 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term509 A B s a t b g f x) = (term510 A B s a t b g f x).
Proof. exact (MK_COMB (@lem5079603 A s x a) (@lem5079601 A B t b g f x)). Qed.
Lemma lem5079605 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term105 A B s a t b g f x) = (term509 A B s a t b g f x).
Proof. exact (@lem17265 (term27 A s x a) (term101 A B t b g f x)). Qed.
Lemma lem5079606 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term105 A B s a t b g f x) = (term510 A B s a t b g f x).
Proof. exact (TRANS (@lem5079605 A B s a t b g f x) (@lem5079604 A B s a t b g f x)). Qed.
Lemma lem5079607 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term107 A B s a t b g f) = (term511 A B s a t b g f).
Proof. exact (fun_ext (fun x : A => @lem5079606 A B s a t b g f x)). Qed.
Lemma lem5079608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5079609 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term109 A B s a t b g f) = (term512 A B s a t b g f).
Proof. exact (MK_COMB (@lem5079608 A) (@lem5079607 A B s a t b g f)). Qed.
Lemma lem5079613 {B : Type'} (y : B) (b : B) : (term501 B y b) = (y = b).
Proof. exact (@lem16933 (y = b)). Qed.
Lemma lem5079615 {B : Type'} (y : B) (t : B -> Prop) : (term502 B y t) = (term502 B y t).
Proof. exact (eq_refl (term502 B y t)). Qed.
Lemma lem5079616 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term503 B t y b) = (term504 B t y b).
Proof. exact (MK_COMB (@lem5079615 B y t) (@lem5079613 B y b)). Qed.
Lemma lem5079617 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term505 B t y b) = (term503 B t y b).
Proof. exact (@lem17045 (@IN B y t) (term506 B y b)). Qed.
Lemma lem5079618 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term505 B t y b) = (term504 B t y b).
Proof. exact (TRANS (@lem5079617 B t y b) (@lem5079616 B t y b)). Qed.
Lemma lem5079627 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term125 A B s a f g y) = (term125 A B s a f g y).
Proof. exact (eq_refl (term125 A B s a f g y)). Qed.
Lemma lem5079628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079629 {B : Type'} (t : B -> Prop) (y : B) (b : B) : (term507 B t y b) = (term508 B t y b).
Proof. exact (MK_COMB (@lem5079628) (@lem5079618 B t y b)). Qed.
Lemma lem5079630 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term513 A B t b s a f g y) = (term514 A B t b s a f g y).
Proof. exact (MK_COMB (@lem5079629 B t y b) (@lem5079627 A B s a f g y)). Qed.
Lemma lem5079631 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term129 A B t b s a f g y) = (term513 A B t b s a f g y).
Proof. exact (@lem17265 (term27 B t y b) (term125 A B s a f g y)). Qed.
Lemma lem5079632 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term129 A B t b s a f g y) = (term514 A B t b s a f g y).
Proof. exact (TRANS (@lem5079631 A B t b s a f g y) (@lem5079630 A B t b s a f g y)). Qed.
Lemma lem5079633 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term131 A B t b s a f g) = (term515 A B t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5079632 A B t b s a f g y)). Qed.
Lemma lem5079634 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5079635 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term133 A B t b s a f g) = (term516 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079634 B) (@lem5079633 A B t b s a f g)). Qed.
Lemma lem5079636 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term706 A B t b s a f g) = (term133 A B t b s a f g).
Proof. exact (@lem16933 (term133 A B t b s a f g)). Qed.
Lemma lem5079637 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term706 A B t b s a f g) = (term516 A B t b s a f g).
Proof. exact (TRANS (@lem5079636 A B t b s a f g) (@lem5079635 A B t b s a f g)). Qed.
Lemma lem5079638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5079639 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term111 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (MK_COMB (@lem5079638) (@lem5079609 A B s a t b g f)). Qed.
Lemma lem5079640 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term707 A B t b s a f g) = (term708 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079639 A B s a t b g f) (@lem5079637 A B t b s a f g)). Qed.
Lemma lem5079641 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term709 A B t b s a f g) = (term707 A B t b s a f g).
Proof. exact (@lem17362 (term109 A B s a t b g f) (term348 A B t b s a f g)). Qed.
Lemma lem5079642 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term709 A B t b s a f g) = (term708 A B t b s a f g).
Proof. exact (TRANS (@lem5079641 A B t b s a f g) (@lem5079640 A B t b s a f g)). Qed.
Lemma lem5079644 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5079645 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term710 A B t b s a f g) = (term711 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079644 B b t) (@lem5079642 A B t b s a f g)). Qed.
Lemma lem5079646 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term712 A B t b s a f g) = (term710 A B t b s a f g).
Proof. exact (@lem17362 (@IN B b t) (term349 A B t b s a f g)). Qed.
Lemma lem5079647 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term712 A B t b s a f g) = (term711 A B t b s a f g).
Proof. exact (TRANS (@lem5079646 A B t b s a f g) (@lem5079645 A B t b s a f g)). Qed.
Lemma lem5079649 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5079650 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term713 A B t b s a f g) = (term714 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079649 A a s) (@lem5079647 A B t b s a f g)). Qed.
Lemma lem5079651 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term715 A B t b s a f g) = (term713 A B t b s a f g).
Proof. exact (@lem17362 (@IN A a s) (term350 A B t b s a f g)). Qed.
Lemma lem5079652 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term715 A B t b s a f g) = (term714 A B t b s a f g).
Proof. exact (TRANS (@lem5079651 A B t b s a f g) (@lem5079650 A B t b s a f g)). Qed.
Lemma lem5079654 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5079655 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term716 A B t b s a f g) = (term717 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079654 A B s t) (@lem5079652 A B t b s a f g)). Qed.
Lemma lem5079656 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term718 A B t b s a f g) = (term716 A B t b s a f g).
Proof. exact (@lem17362 ((@CARD A s) = (@CARD B t)) (term351 A B t b s a f g)). Qed.
Lemma lem5079657 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term718 A B t b s a f g) = (term717 A B t b s a f g).
Proof. exact (TRANS (@lem5079656 A B t b s a f g) (@lem5079655 A B t b s a f g)). Qed.
Lemma lem5079659 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5079660 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term719 A B t b s a f g) = (term720 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079659 B t) (@lem5079657 A B t b s a f g)). Qed.
Lemma lem5079661 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term721 A B t b s a f g) = (term719 A B t b s a f g).
Proof. exact (@lem17362 (@FINITE B t) (term352 A B t b s a f g)). Qed.
Lemma lem5079662 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term721 A B t b s a f g) = (term720 A B t b s a f g).
Proof. exact (TRANS (@lem5079661 A B t b s a f g) (@lem5079660 A B t b s a f g)). Qed.
Lemma lem5079664 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5079665 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term722 A B t b s a f g) = (term723 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079664 A s) (@lem5079662 A B t b s a f g)). Qed.
Lemma lem5079666 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term724 A B t b s a f g) = (term722 A B t b s a f g).
Proof. exact (@lem17362 (@FINITE A s) (term353 A B t b s a f g)). Qed.
Lemma lem5079667 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term724 A B t b s a f g) = (term723 A B t b s a f g).
Proof. exact (TRANS (@lem5079666 A B t b s a f g) (@lem5079665 A B t b s a f g)). Qed.
Lemma lem5079668 {B : Type'} (P : type686 B) : (term668 B P) = (term669 B P).
Proof. exact (@lem18392 (B -> Prop) P). Qed.
Lemma lem5079669 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term725 A B b s a f g) = (term726 A B b s a f g).
Proof. exact (@lem5079668 B (term355 A B b s a f g)). Qed.
Lemma lem5079670 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term727 A B b s a f g t) = (term354 A B t b s a f g).
Proof. exact (eq_refl (term727 A B b s a f g t)). Qed.
Lemma lem5079671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079672 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term728 A B b s a f g t) = (term724 A B t b s a f g).
Proof. exact (MK_COMB (@lem5079671) (@lem5079670 A B t b s a f g)). Qed.
Lemma lem5079673 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term728 A B b s a f g t) = (term723 A B t b s a f g).
Proof. exact (TRANS (@lem5079672 A B t b s a f g) (@lem5079667 A B t b s a f g)). Qed.
Lemma lem5079674 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term729 A B b s a f g) = (term730 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5079673 A B t b s a f g)). Qed.
Lemma lem5079675 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5079676 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term726 A B b s a f g) = (term731 A B b s a f g).
Proof. exact (MK_COMB (@lem5079675 B) (@lem5079674 A B b s a f g)). Qed.
Lemma lem5079677 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term725 A B b s a f g) = (term731 A B b s a f g).
Proof. exact (TRANS (@lem5079669 A B b s a f g) (@lem5079676 A B b s a f g)). Qed.
Lemma lem5079678 {A : Type'} (P : type686 A) : (term668 A P) = (term669 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem5079679 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term732 A B b a f g) = (term733 A B b a f g).
Proof. exact (@lem5079678 A (term357 A B b a f g)). Qed.
Lemma lem5079680 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term734 A B b a f g s) = (term356 A B b s a f g).
Proof. exact (eq_refl (term734 A B b a f g s)). Qed.
Lemma lem5079681 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079682 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term735 A B b a f g s) = (term725 A B b s a f g).
Proof. exact (MK_COMB (@lem5079681) (@lem5079680 A B b s a f g)). Qed.
Lemma lem5079683 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term735 A B b a f g s) = (term731 A B b s a f g).
Proof. exact (TRANS (@lem5079682 A B b s a f g) (@lem5079677 A B b s a f g)). Qed.
Lemma lem5079684 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term736 A B b a f g) = (term737 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5079683 A B b s a f g)). Qed.
Lemma lem5079685 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5079686 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term733 A B b a f g) = (term738 A B b a f g).
Proof. exact (MK_COMB (@lem5079685 A) (@lem5079684 A B b a f g)). Qed.
Lemma lem5079687 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term732 A B b a f g) = (term738 A B b a f g).
Proof. exact (TRANS (@lem5079679 A B b a f g) (@lem5079686 A B b a f g)). Qed.
Lemma lem5079688 {A B : Type'} (P : type572 A B) : (term684 A B P) = (term685 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem5079689 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term739 A B b a g) = (term740 A B b a g).
Proof. exact (@lem5079688 A B (term359 A B b a g)). Qed.
Lemma lem5079690 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term741 A B b a g f) = (term358 A B b a f g).
Proof. exact (eq_refl (term741 A B b a g f)). Qed.
Lemma lem5079691 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079692 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term742 A B b a g f) = (term732 A B b a f g).
Proof. exact (MK_COMB (@lem5079691) (@lem5079690 A B b a f g)). Qed.
Lemma lem5079693 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term742 A B b a g f) = (term738 A B b a f g).
Proof. exact (TRANS (@lem5079692 A B b a f g) (@lem5079687 A B b a f g)). Qed.
Lemma lem5079694 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term743 A B b a g) = (term744 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5079693 A B b a f g)). Qed.
Lemma lem5079695 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5079696 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term740 A B b a g) = (term745 A B b a g).
Proof. exact (MK_COMB (@lem5079695 A B) (@lem5079694 A B b a g)). Qed.
Lemma lem5079697 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term739 A B b a g) = (term745 A B b a g).
Proof. exact (TRANS (@lem5079689 A B b a g) (@lem5079696 A B b a g)). Qed.
Lemma lem5079698 {B : Type'} (P : B -> Prop) : (term570 B P) = (term571 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5079699 {A B : Type'} (a : A) (g : B -> A) : (term746 A B a g) = (term747 A B a g).
Proof. exact (@lem5079698 B (term361 A B a g)). Qed.
Lemma lem5079700 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term748 A B a g b) = (term360 A B b a g).
Proof. exact (eq_refl (term748 A B a g b)). Qed.
Lemma lem5079701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5079702 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term749 A B a g b) = (term739 A B b a g).
Proof. exact (MK_COMB (@lem5079701) (@lem5079700 A B b a g)). Qed.
Lemma lem5079703 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term749 A B a g b) = (term745 A B b a g).
Proof. exact (TRANS (@lem5079702 A B b a g) (@lem5079697 A B b a g)). Qed.
Lemma lem5079704 {A B : Type'} (a : A) (g : B -> A) : (term750 A B a g) = (term751 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5079703 A B b a g)). Qed.
Lemma lem5079705 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5079706 {A B : Type'} (a : A) (g : B -> A) : (term747 A B a g) = (term752 A B a g).
Proof. exact (MK_COMB (@lem5079705 B) (@lem5079704 A B a g)). Qed.
Lemma lem5079707 {A B : Type'} (a : A) (g : B -> A) : (term746 A B a g) = (term752 A B a g).
Proof. exact (TRANS (@lem5079699 A B a g) (@lem5079706 A B a g)). Qed.
Lemma lem5079709 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5079710 {A B : Type'} (a : A) (g : B -> A) : (term754 A B a g) = (term755 A B a g).
Proof. exact (MK_COMB (@lem5079709 A a) (@lem5079707 A B a g)). Qed.
Lemma lem5079711 {A B : Type'} (a : A) (g : B -> A) : (term756 A B a g) = (term754 A B a g).
Proof. exact (@lem17160 (a = a) (term362 A B a g)). Qed.
Lemma lem5079712 {A B : Type'} (a : A) (g : B -> A) : (term756 A B a g) = (term755 A B a g).
Proof. exact (TRANS (@lem5079711 A B a g) (@lem5079710 A B a g)). Qed.
Lemma lem5079713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079714 {A B : Type'} (a : A) (g : B -> A) : (term757 A B a g) = (term758 A B a g).
Proof. exact (MK_COMB (@lem5079713) (@lem5079577 A B a g)). Qed.
Lemma lem5079715 {A B : Type'} (a : A) (g : B -> A) : (term759 A B a g) = (term760 A B a g).
Proof. exact (MK_COMB (@lem5079714 A B a g) (@lem5079712 A B a g)). Qed.
Lemma lem5079716 {A B : Type'} (a : A) (g : B -> A) : (term499 A B a g) = (term759 A B a g).
Proof. exact (@lem17045 (term489 A B a g) (term387 A B a g)). Qed.
Lemma lem5079717 {A B : Type'} (a : A) (g : B -> A) : (term499 A B a g) = (term760 A B a g).
Proof. exact (TRANS (@lem5079716 A B a g) (@lem5079715 A B a g)). Qed.
Lemma lem5079731 {A : Type'} (P : Prop) (Q : A -> Prop) : (term761 A P Q) = (term762 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5079732 {B : Type'} (P : Prop) (Q : type686 B) : (term763 B P Q) = (term764 B P Q).
Proof. exact (@lem5079731 (B -> Prop) P Q). Qed.
Lemma lem5079733 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term765 A B a b s f g) = (term766 A B a b s f g).
Proof. exact (@lem5079732 B (@FINITE A s) (term767 A B a b s f g)). Qed.
Lemma lem5079734 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term768 A B a b s f g t) = (term663 A B a b t s f g).
Proof. exact (eq_refl (term768 A B a b s f g t)). Qed.
Lemma lem5079735 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5079736 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term769 A B a b s f g t) = (term666 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079735 A s) (@lem5079734 A B a b t s f g)). Qed.
Lemma lem5079737 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term770 A B a b s f g) = (term675 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5079736 A B a b t s f g)). Qed.
Lemma lem5079738 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5079739 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term765 A B a b s f g) = (term676 A B a b s f g).
Proof. exact (MK_COMB (@lem5079738 B) (@lem5079737 A B a b s f g)). Qed.
Lemma lem5079740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5079741 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term771 A B a b s f g) = (term772 A B a b s f g).
Proof. exact (MK_COMB (@lem5079740) (@lem5079739 A B a b s f g)). Qed.
Lemma lem5079742 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term768 A B a b s f g t) = (term663 A B a b t s f g).
Proof. exact (eq_refl (term768 A B a b s f g t)). Qed.
Lemma lem5079743 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term773 A B a b s f g) = (term767 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5079742 A B a b t s f g)). Qed.
Lemma lem5079744 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5079745 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term774 A B a b s f g) = (term775 A B a b s f g).
Proof. exact (MK_COMB (@lem5079744 B) (@lem5079743 A B a b s f g)). Qed.
Lemma lem5079746 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5079747 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term766 A B a b s f g) = (term776 A B a b s f g).
Proof. exact (MK_COMB (@lem5079746 A s) (@lem5079745 A B a b s f g)). Qed.
Lemma lem5079748 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term765 A B a b s f g) = (term766 A B a b s f g)) = ((term676 A B a b s f g) = (term776 A B a b s f g)).
Proof. exact (MK_COMB (@lem5079741 A B a b s f g) (@lem5079747 A B a b s f g)). Qed.
Lemma lem5079749 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term676 A B a b s f g) = (term776 A B a b s f g).
Proof. exact (EQ_MP (@lem5079748 A B a b s f g) (@lem5079733 A B a b s f g)). Qed.
Lemma lem5079875 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5079876 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (@lem5079875 A P Q). Qed.
Lemma lem5079877 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term779 A B b a s t g f) = (term780 A B b a s t g f).
Proof. exact (@lem5079876 A (term781 A B b s f t a) (term782 A B b a s t g f)). Qed.
Lemma lem5079878 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term783 A B b s f t a x) = (term545 A B b s f t a x).
Proof. exact (eq_refl (term783 A B b s f t a x)). Qed.
Lemma lem5079879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079880 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term784 A B b s f t a x) = (term564 A B b s f t a x).
Proof. exact (MK_COMB (@lem5079879) (@lem5079878 A B b s f t a x)). Qed.
Lemma lem5079881 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term785 A B b a s t g f x) = (term561 A B b a s t g f x).
Proof. exact (eq_refl (term785 A B b a s t g f x)). Qed.
Lemma lem5079882 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term786 A B b a s t g f x) = (term566 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5079880 A B b s f t a x) (@lem5079881 A B b a s t g f x)). Qed.
Lemma lem5079883 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term787 A B b a s t g f) = (term577 A B b a s t g f).
Proof. exact (fun_ext (fun x : A => @lem5079882 A B b a s t g f x)). Qed.
Lemma lem5079884 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5079885 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term779 A B b a s t g f) = (term578 A B b a s t g f).
Proof. exact (MK_COMB (@lem5079884 A) (@lem5079883 A B b a s t g f)). Qed.
Lemma lem5079886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5079887 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term788 A B b a s t g f) = (term789 A B b a s t g f).
Proof. exact (MK_COMB (@lem5079886) (@lem5079885 A B b a s t g f)). Qed.
Lemma lem5079888 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term783 A B b s f t a x) = (term545 A B b s f t a x).
Proof. exact (eq_refl (term783 A B b s f t a x)). Qed.
Lemma lem5079889 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) : (term790 A B b s f t a) = (term781 A B b s f t a).
Proof. exact (fun_ext (fun x : A => @lem5079888 A B b s f t a x)). Qed.
Lemma lem5079890 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5079891 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) : (term791 A B b s f t a) = (term792 A B b s f t a).
Proof. exact (MK_COMB (@lem5079890 A) (@lem5079889 A B b s f t a)). Qed.
Lemma lem5079892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079893 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) : (term793 A B b s f t a) = (term794 A B b s f t a).
Proof. exact (MK_COMB (@lem5079892) (@lem5079891 A B b s f t a)). Qed.
Lemma lem5079894 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term785 A B b a s t g f x) = (term561 A B b a s t g f x).
Proof. exact (eq_refl (term785 A B b a s t g f x)). Qed.
Lemma lem5079895 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term795 A B b a s t g f) = (term782 A B b a s t g f).
Proof. exact (fun_ext (fun x : A => @lem5079894 A B b a s t g f x)). Qed.
Lemma lem5079896 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5079897 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term796 A B b a s t g f) = (term797 A B b a s t g f).
Proof. exact (MK_COMB (@lem5079896 A) (@lem5079895 A B b a s t g f)). Qed.
Lemma lem5079898 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term780 A B b a s t g f) = (term798 A B b a s t g f).
Proof. exact (MK_COMB (@lem5079893 A B b s f t a) (@lem5079897 A B b a s t g f)). Qed.
Lemma lem5079899 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : ((term779 A B b a s t g f) = (term780 A B b a s t g f)) = ((term578 A B b a s t g f) = (term798 A B b a s t g f)).
Proof. exact (MK_COMB (@lem5079887 A B b a s t g f) (@lem5079898 A B b a s t g f)). Qed.
Lemma lem5079900 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term578 A B b a s t g f) = (term798 A B b a s t g f).
Proof. exact (EQ_MP (@lem5079899 A B b a s t g f) (@lem5079877 A B b a s t g f)). Qed.
Lemma lem5079997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5079998 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term638 A B b a s t g f) = (term799 A B b a s t g f).
Proof. exact (MK_COMB (@lem5079997) (@lem5079900 A B b a s t g f)). Qed.
Lemma lem5080000 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term777 A P Q) = (term778 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5080001 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term777 B P Q) = (term778 B P Q).
Proof. exact (@lem5080000 B P Q). Qed.
Lemma lem5080002 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term800 A B a b t s f g) = (term801 A B a b t s f g).
Proof. exact (@lem5080001 B (term802 A B a t g s b) (term803 A B a b t s f g)). Qed.
Lemma lem5080003 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term804 A B a t g s b y) = (term605 A B a t g s b y).
Proof. exact (eq_refl (term804 A B a t g s b y)). Qed.
Lemma lem5080004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080005 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term805 A B a t g s b y) = (term624 A B a t g s b y).
Proof. exact (MK_COMB (@lem5080004) (@lem5080003 A B a t g s b y)). Qed.
Lemma lem5080006 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term806 A B a b t s f g y) = (term621 A B a b t s f g y).
Proof. exact (eq_refl (term806 A B a b t s f g y)). Qed.
Lemma lem5080007 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term807 A B a b t s f g y) = (term626 A B a b t s f g y).
Proof. exact (MK_COMB (@lem5080005 A B a t g s b y) (@lem5080006 A B a b t s f g y)). Qed.
Lemma lem5080008 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term808 A B a b t s f g) = (term635 A B a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080007 A B a b t s f g y)). Qed.
Lemma lem5080009 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080010 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term800 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080009 B) (@lem5080008 A B a b t s f g)). Qed.
Lemma lem5080011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080012 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term809 A B a b t s f g) = (term810 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080011) (@lem5080010 A B a b t s f g)). Qed.
Lemma lem5080013 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term804 A B a t g s b y) = (term605 A B a t g s b y).
Proof. exact (eq_refl (term804 A B a t g s b y)). Qed.
Lemma lem5080014 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) : (term811 A B a t g s b) = (term802 A B a t g s b).
Proof. exact (fun_ext (fun y : B => @lem5080013 A B a t g s b y)). Qed.
Lemma lem5080015 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080016 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) : (term812 A B a t g s b) = (term813 A B a t g s b).
Proof. exact (MK_COMB (@lem5080015 B) (@lem5080014 A B a t g s b)). Qed.
Lemma lem5080017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080018 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) : (term814 A B a t g s b) = (term815 A B a t g s b).
Proof. exact (MK_COMB (@lem5080017) (@lem5080016 A B a t g s b)). Qed.
Lemma lem5080019 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term806 A B a b t s f g y) = (term621 A B a b t s f g y).
Proof. exact (eq_refl (term806 A B a b t s f g y)). Qed.
Lemma lem5080020 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term816 A B a b t s f g) = (term803 A B a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080019 A B a b t s f g y)). Qed.
Lemma lem5080021 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080022 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term817 A B a b t s f g) = (term818 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080021 B) (@lem5080020 A B a b t s f g)). Qed.
Lemma lem5080023 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term801 A B a b t s f g) = (term819 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080018 A B a t g s b) (@lem5080022 A B a b t s f g)). Qed.
Lemma lem5080024 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term800 A B a b t s f g) = (term801 A B a b t s f g)) = ((term636 A B a b t s f g) = (term819 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080012 A B a b t s f g) (@lem5080023 A B a b t s f g)). Qed.
Lemma lem5080025 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term636 A B a b t s f g) = (term819 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080024 A B a b t s f g) (@lem5080002 A B a b t s f g)). Qed.
Lemma lem5080122 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term640 A B a b t s f g) = (term820 A B a b t s f g).
Proof. exact (MK_COMB (@lem5079998 A B b a s t g f) (@lem5080025 A B a b t s f g)). Qed.
Lemma lem5080123 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term643 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (eq_refl (term643 A B t b s a f g)). Qed.
Lemma lem5080124 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term645 A B a b t s f g) = (term821 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080123 A B t b s a f g) (@lem5080122 A B a b t s f g)). Qed.
Lemma lem5080125 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (eq_refl (term647 A B s a t b g f)). Qed.
Lemma lem5080126 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term649 A B a b t s f g) = (term822 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080125 A B s a t b g f) (@lem5080124 A B a b t s f g)). Qed.
Lemma lem5080127 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5080128 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term652 A B a b t s f g) = (term823 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080127 B b t) (@lem5080126 A B a b t s f g)). Qed.
Lemma lem5080129 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5080130 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term655 A B a b t s f g) = (term824 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080129 A a s) (@lem5080128 A B a b t s f g)). Qed.
Lemma lem5080131 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5080132 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term659 A B a b t s f g) = (term825 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080131 A B s t) (@lem5080130 A B a b t s f g)). Qed.
Lemma lem5080133 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5080134 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term663 A B a b t s f g) = (term826 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080133 B t) (@lem5080132 A B a b t s f g)). Qed.
Lemma lem5080135 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term767 A B a b s f g) = (term827 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080134 A B a b t s f g)). Qed.
Lemma lem5080136 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080137 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term775 A B a b s f g) = (term828 A B a b s f g).
Proof. exact (MK_COMB (@lem5080136 B) (@lem5080135 A B a b s f g)). Qed.
Lemma lem5080166 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080167 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term776 A B a b s f g) = (term829 A B a b s f g).
Proof. exact (MK_COMB (@lem5080166 A s) (@lem5080137 A B a b s f g)). Qed.
Lemma lem5080168 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term676 A B a b s f g) = (term829 A B a b s f g).
Proof. exact (TRANS (@lem5079749 A B a b s f g) (@lem5080167 A B a b s f g)). Qed.
Lemma lem5080169 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term682 A B a b f g) = (term830 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5080168 A B a b s f g)). Qed.
Lemma lem5080170 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5080171 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term683 A B a b f g) = (term831 A B a b f g).
Proof. exact (MK_COMB (@lem5080170 A) (@lem5080169 A B a b f g)). Qed.
Lemma lem5080200 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term691 A B a b g) = (term832 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5080171 A B a b f g)). Qed.
Lemma lem5080201 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5080202 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term692 A B a b g) = (term833 A B a b g).
Proof. exact (MK_COMB (@lem5080201 A B) (@lem5080200 A B a b g)). Qed.
Lemma lem5080207 {A B : Type'} (a : A) (g : B -> A) : (term698 A B a g) = (term834 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5080202 A B a b g)). Qed.
Lemma lem5080208 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080209 {A B : Type'} (a : A) (g : B -> A) : (term699 A B a g) = (term835 A B a g).
Proof. exact (MK_COMB (@lem5080208 B) (@lem5080207 A B a g)). Qed.
Lemma lem5080214 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080215 {A B : Type'} (a : A) (g : B -> A) : (term703 A B a g) = (term836 A B a g).
Proof. exact (MK_COMB (@lem5080214 A a) (@lem5080209 A B a g)). Qed.
Lemma lem5080216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080217 {A B : Type'} (a : A) (g : B -> A) : (term758 A B a g) = (term837 A B a g).
Proof. exact (MK_COMB (@lem5080216) (@lem5080215 A B a g)). Qed.
Lemma lem5080231 {A : Type'} (P : Prop) (Q : A -> Prop) : (term761 A P Q) = (term762 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5080232 {B : Type'} (P : Prop) (Q : type686 B) : (term763 B P Q) = (term764 B P Q).
Proof. exact (@lem5080231 (B -> Prop) P Q). Qed.
Lemma lem5080233 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term838 A B b s a f g) = (term839 A B b s a f g).
Proof. exact (@lem5080232 B (@FINITE A s) (term840 A B b s a f g)). Qed.
Lemma lem5080234 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term841 A B b s a f g t) = (term720 A B t b s a f g).
Proof. exact (eq_refl (term841 A B b s a f g t)). Qed.
Lemma lem5080235 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080236 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term842 A B b s a f g t) = (term723 A B t b s a f g).
Proof. exact (MK_COMB (@lem5080235 A s) (@lem5080234 A B t b s a f g)). Qed.
Lemma lem5080237 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term843 A B b s a f g) = (term730 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080236 A B t b s a f g)). Qed.
Lemma lem5080238 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080239 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term838 A B b s a f g) = (term731 A B b s a f g).
Proof. exact (MK_COMB (@lem5080238 B) (@lem5080237 A B b s a f g)). Qed.
Lemma lem5080240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080241 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term844 A B b s a f g) = (term845 A B b s a f g).
Proof. exact (MK_COMB (@lem5080240) (@lem5080239 A B b s a f g)). Qed.
Lemma lem5080242 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term841 A B b s a f g t) = (term720 A B t b s a f g).
Proof. exact (eq_refl (term841 A B b s a f g t)). Qed.
Lemma lem5080243 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term846 A B b s a f g) = (term840 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080242 A B t b s a f g)). Qed.
Lemma lem5080244 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080245 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term847 A B b s a f g) = (term848 A B b s a f g).
Proof. exact (MK_COMB (@lem5080244 B) (@lem5080243 A B b s a f g)). Qed.
Lemma lem5080246 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080247 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term839 A B b s a f g) = (term849 A B b s a f g).
Proof. exact (MK_COMB (@lem5080246 A s) (@lem5080245 A B b s a f g)). Qed.
Lemma lem5080248 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : ((term838 A B b s a f g) = (term839 A B b s a f g)) = ((term731 A B b s a f g) = (term849 A B b s a f g)).
Proof. exact (MK_COMB (@lem5080241 A B b s a f g) (@lem5080247 A B b s a f g)). Qed.
Lemma lem5080249 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term731 A B b s a f g) = (term849 A B b s a f g).
Proof. exact (EQ_MP (@lem5080248 A B b s a f g) (@lem5080233 A B b s a f g)). Qed.
Lemma lem5080374 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term737 A B b a f g) = (term850 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5080249 A B b s a f g)). Qed.
Lemma lem5080375 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5080376 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term738 A B b a f g) = (term851 A B b a f g).
Proof. exact (MK_COMB (@lem5080375 A) (@lem5080374 A B b a f g)). Qed.
Lemma lem5080405 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term744 A B b a g) = (term852 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5080376 A B b a f g)). Qed.
Lemma lem5080406 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5080407 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term745 A B b a g) = (term853 A B b a g).
Proof. exact (MK_COMB (@lem5080406 A B) (@lem5080405 A B b a g)). Qed.
Lemma lem5080412 {A B : Type'} (a : A) (g : B -> A) : (term751 A B a g) = (term854 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5080407 A B b a g)). Qed.
Lemma lem5080413 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080414 {A B : Type'} (a : A) (g : B -> A) : (term752 A B a g) = (term855 A B a g).
Proof. exact (MK_COMB (@lem5080413 B) (@lem5080412 A B a g)). Qed.
Lemma lem5080419 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5080420 {A B : Type'} (a : A) (g : B -> A) : (term755 A B a g) = (term856 A B a g).
Proof. exact (MK_COMB (@lem5080419 A a) (@lem5080414 A B a g)). Qed.
Lemma lem5080421 {A B : Type'} (a : A) (g : B -> A) : (term760 A B a g) = (term857 A B a g).
Proof. exact (MK_COMB (@lem5080217 A B a g) (@lem5080420 A B a g)). Qed.
Lemma lem5080423 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term778 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5080424 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term778 A P Q) = (term777 A P Q).
Proof. exact (@lem5080423 A P Q). Qed.
Lemma lem5080425 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term780 A B b a s t g f) = (term779 A B b a s t g f).
Proof. exact (@lem5080424 A (term781 A B b s f t a) (term782 A B b a s t g f)). Qed.
Lemma lem5080426 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term783 A B b s f t a x) = (term545 A B b s f t a x).
Proof. exact (eq_refl (term783 A B b s f t a x)). Qed.
Lemma lem5080427 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) : (term790 A B b s f t a) = (term781 A B b s f t a).
Proof. exact (fun_ext (fun x : A => @lem5080426 A B b s f t a x)). Qed.
Lemma lem5080428 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080429 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) : (term791 A B b s f t a) = (term792 A B b s f t a).
Proof. exact (MK_COMB (@lem5080428 A) (@lem5080427 A B b s f t a)). Qed.
Lemma lem5080430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080431 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) : (term793 A B b s f t a) = (term794 A B b s f t a).
Proof. exact (MK_COMB (@lem5080430) (@lem5080429 A B b s f t a)). Qed.
Lemma lem5080432 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term785 A B b a s t g f x) = (term561 A B b a s t g f x).
Proof. exact (eq_refl (term785 A B b a s t g f x)). Qed.
Lemma lem5080433 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term795 A B b a s t g f) = (term782 A B b a s t g f).
Proof. exact (fun_ext (fun x : A => @lem5080432 A B b a s t g f x)). Qed.
Lemma lem5080434 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080435 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term796 A B b a s t g f) = (term797 A B b a s t g f).
Proof. exact (MK_COMB (@lem5080434 A) (@lem5080433 A B b a s t g f)). Qed.
Lemma lem5080436 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term780 A B b a s t g f) = (term798 A B b a s t g f).
Proof. exact (MK_COMB (@lem5080431 A B b s f t a) (@lem5080435 A B b a s t g f)). Qed.
Lemma lem5080437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080438 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term858 A B b a s t g f) = (term859 A B b a s t g f).
Proof. exact (MK_COMB (@lem5080437) (@lem5080436 A B b a s t g f)). Qed.
Lemma lem5080439 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term783 A B b s f t a x) = (term545 A B b s f t a x).
Proof. exact (eq_refl (term783 A B b s f t a x)). Qed.
Lemma lem5080440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080441 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) : (term784 A B b s f t a x) = (term564 A B b s f t a x).
Proof. exact (MK_COMB (@lem5080440) (@lem5080439 A B b s f t a x)). Qed.
Lemma lem5080442 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term785 A B b a s t g f x) = (term561 A B b a s t g f x).
Proof. exact (eq_refl (term785 A B b a s t g f x)). Qed.
Lemma lem5080443 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term786 A B b a s t g f x) = (term566 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5080441 A B b s f t a x) (@lem5080442 A B b a s t g f x)). Qed.
Lemma lem5080444 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term787 A B b a s t g f) = (term577 A B b a s t g f).
Proof. exact (fun_ext (fun x : A => @lem5080443 A B b a s t g f x)). Qed.
Lemma lem5080445 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080446 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term779 A B b a s t g f) = (term578 A B b a s t g f).
Proof. exact (MK_COMB (@lem5080445 A) (@lem5080444 A B b a s t g f)). Qed.
Lemma lem5080447 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : ((term780 A B b a s t g f) = (term779 A B b a s t g f)) = ((term798 A B b a s t g f) = (term578 A B b a s t g f)).
Proof. exact (MK_COMB (@lem5080438 A B b a s t g f) (@lem5080446 A B b a s t g f)). Qed.
Lemma lem5080448 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term798 A B b a s t g f) = (term578 A B b a s t g f).
Proof. exact (EQ_MP (@lem5080447 A B b a s t g f) (@lem5080425 A B b a s t g f)). Qed.
Lemma lem5080449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080450 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term799 A B b a s t g f) = (term638 A B b a s t g f).
Proof. exact (MK_COMB (@lem5080449) (@lem5080448 A B b a s t g f)). Qed.
Lemma lem5080452 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term778 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5080453 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term778 B P Q) = (term777 B P Q).
Proof. exact (@lem5080452 B P Q). Qed.
Lemma lem5080454 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term801 A B a b t s f g) = (term800 A B a b t s f g).
Proof. exact (@lem5080453 B (term802 A B a t g s b) (term803 A B a b t s f g)). Qed.
Lemma lem5080455 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term804 A B a t g s b y) = (term605 A B a t g s b y).
Proof. exact (eq_refl (term804 A B a t g s b y)). Qed.
Lemma lem5080456 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) : (term811 A B a t g s b) = (term802 A B a t g s b).
Proof. exact (fun_ext (fun y : B => @lem5080455 A B a t g s b y)). Qed.
Lemma lem5080457 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080458 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) : (term812 A B a t g s b) = (term813 A B a t g s b).
Proof. exact (MK_COMB (@lem5080457 B) (@lem5080456 A B a t g s b)). Qed.
Lemma lem5080459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080460 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) : (term814 A B a t g s b) = (term815 A B a t g s b).
Proof. exact (MK_COMB (@lem5080459) (@lem5080458 A B a t g s b)). Qed.
Lemma lem5080461 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term806 A B a b t s f g y) = (term621 A B a b t s f g y).
Proof. exact (eq_refl (term806 A B a b t s f g y)). Qed.
Lemma lem5080462 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term816 A B a b t s f g) = (term803 A B a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080461 A B a b t s f g y)). Qed.
Lemma lem5080463 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080464 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term817 A B a b t s f g) = (term818 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080463 B) (@lem5080462 A B a b t s f g)). Qed.
Lemma lem5080465 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term801 A B a b t s f g) = (term819 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080460 A B a t g s b) (@lem5080464 A B a b t s f g)). Qed.
Lemma lem5080466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080467 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term860 A B a b t s f g) = (term861 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080466) (@lem5080465 A B a b t s f g)). Qed.
Lemma lem5080468 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term804 A B a t g s b y) = (term605 A B a t g s b y).
Proof. exact (eq_refl (term804 A B a t g s b y)). Qed.
Lemma lem5080469 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080470 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) : (term805 A B a t g s b y) = (term624 A B a t g s b y).
Proof. exact (MK_COMB (@lem5080469) (@lem5080468 A B a t g s b y)). Qed.
Lemma lem5080471 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term806 A B a b t s f g y) = (term621 A B a b t s f g y).
Proof. exact (eq_refl (term806 A B a b t s f g y)). Qed.
Lemma lem5080472 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term807 A B a b t s f g y) = (term626 A B a b t s f g y).
Proof. exact (MK_COMB (@lem5080470 A B a t g s b y) (@lem5080471 A B a b t s f g y)). Qed.
Lemma lem5080473 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term808 A B a b t s f g) = (term635 A B a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080472 A B a b t s f g y)). Qed.
Lemma lem5080474 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080475 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term800 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080474 B) (@lem5080473 A B a b t s f g)). Qed.
Lemma lem5080476 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term801 A B a b t s f g) = (term800 A B a b t s f g)) = ((term819 A B a b t s f g) = (term636 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080467 A B a b t s f g) (@lem5080475 A B a b t s f g)). Qed.
Lemma lem5080477 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term819 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080476 A B a b t s f g) (@lem5080454 A B a b t s f g)). Qed.
Lemma lem5080478 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term820 A B a b t s f g) = (term640 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080450 A B b a s t g f) (@lem5080477 A B a b t s f g)). Qed.
Lemma lem5080482 {A : Type'} (P : A -> Prop) (Q : Prop) : (term862 A P Q) = (term863 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5080483 {A : Type'} (P : A -> Prop) (Q : Prop) : (term862 A P Q) = (term863 A P Q).
Proof. exact (@lem5080482 A P Q). Qed.
Lemma lem5080484 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term864 A B a b t s f g) = (term865 A B a b t s f g).
Proof. exact (@lem5080483 A (term577 A B b a s t g f) (term636 A B a b t s f g)). Qed.
Lemma lem5080485 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term866 A B b a s t g f x) = (term566 A B b a s t g f x).
Proof. exact (eq_refl (term866 A B b a s t g f x)). Qed.
Lemma lem5080486 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term867 A B b a s t g f) = (term577 A B b a s t g f).
Proof. exact (fun_ext (fun x : A => @lem5080485 A B b a s t g f x)). Qed.
Lemma lem5080487 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080488 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term868 A B b a s t g f) = (term578 A B b a s t g f).
Proof. exact (MK_COMB (@lem5080487 A) (@lem5080486 A B b a s t g f)). Qed.
Lemma lem5080489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080490 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term869 A B b a s t g f) = (term638 A B b a s t g f).
Proof. exact (MK_COMB (@lem5080489) (@lem5080488 A B b a s t g f)). Qed.
Lemma lem5080491 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term636 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (eq_refl (term636 A B a b t s f g)). Qed.
Lemma lem5080492 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term864 A B a b t s f g) = (term640 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080490 A B b a s t g f) (@lem5080491 A B a b t s f g)). Qed.
Lemma lem5080493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080494 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term870 A B a b t s f g) = (term871 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080493) (@lem5080492 A B a b t s f g)). Qed.
Lemma lem5080495 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term866 A B b a s t g f x) = (term566 A B b a s t g f x).
Proof. exact (eq_refl (term866 A B b a s t g f x)). Qed.
Lemma lem5080496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5080497 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term872 A B b a s t g f x) = (term873 A B b a s t g f x).
Proof. exact (MK_COMB (@lem5080496) (@lem5080495 A B b a s t g f x)). Qed.
Lemma lem5080498 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term636 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (eq_refl (term636 A B a b t s f g)). Qed.
Lemma lem5080499 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term874 A B x a b t s f g) = (term875 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080497 A B b a s t g f x) (@lem5080498 A B a b t s f g)). Qed.
Lemma lem5080500 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term876 A B a b t s f g) = (term877 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080499 A B x a b t s f g)). Qed.
Lemma lem5080501 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080502 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term865 A B a b t s f g) = (term878 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080501 A) (@lem5080500 A B a b t s f g)). Qed.
Lemma lem5080503 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term864 A B a b t s f g) = (term865 A B a b t s f g)) = ((term640 A B a b t s f g) = (term878 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080494 A B a b t s f g) (@lem5080502 A B a b t s f g)). Qed.
Lemma lem5080504 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term640 A B a b t s f g) = (term878 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080503 A B a b t s f g) (@lem5080484 A B a b t s f g)). Qed.
Lemma lem5080506 {A : Type'} (P : Prop) (Q : A -> Prop) : (term879 A P Q) = (term880 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5080507 {B : Type'} (P : Prop) (Q : B -> Prop) : (term879 B P Q) = (term880 B P Q).
Proof. exact (@lem5080506 B P Q). Qed.
Lemma lem5080508 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term881 A B x a b t s f g) = (term882 A B x a b t s f g).
Proof. exact (@lem5080507 B (term566 A B b a s t g f x) (term635 A B a b t s f g)). Qed.
Lemma lem5080509 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term883 A B a b t s f g y) = (term626 A B a b t s f g y).
Proof. exact (eq_refl (term883 A B a b t s f g y)). Qed.
Lemma lem5080510 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term884 A B a b t s f g) = (term635 A B a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080509 A B a b t s f g y)). Qed.
Lemma lem5080511 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080512 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term885 A B a b t s f g) = (term636 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080511 B) (@lem5080510 A B a b t s f g)). Qed.
Lemma lem5080513 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term873 A B b a s t g f x) = (term873 A B b a s t g f x).
Proof. exact (eq_refl (term873 A B b a s t g f x)). Qed.
Lemma lem5080514 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term881 A B x a b t s f g) = (term875 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080513 A B b a s t g f x) (@lem5080512 A B a b t s f g)). Qed.
Lemma lem5080515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080516 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term886 A B x a b t s f g) = (term887 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080515) (@lem5080514 A B x a b t s f g)). Qed.
Lemma lem5080517 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term883 A B a b t s f g y) = (term626 A B a b t s f g y).
Proof. exact (eq_refl (term883 A B a b t s f g y)). Qed.
Lemma lem5080518 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term873 A B b a s t g f x) = (term873 A B b a s t g f x).
Proof. exact (eq_refl (term873 A B b a s t g f x)). Qed.
Lemma lem5080519 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term888 A B x a b t s f g y) = (term889 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080518 A B b a s t g f x) (@lem5080517 A B a b t s f g y)). Qed.
Lemma lem5080520 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term890 A B x a b t s f g) = (term891 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080519 A B x a b t s f g y)). Qed.
Lemma lem5080521 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080522 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term882 A B x a b t s f g) = (term892 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080521 B) (@lem5080520 A B x a b t s f g)). Qed.
Lemma lem5080523 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term881 A B x a b t s f g) = (term882 A B x a b t s f g)) = ((term875 A B x a b t s f g) = (term892 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080516 A B x a b t s f g) (@lem5080522 A B x a b t s f g)). Qed.
Lemma lem5080524 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term875 A B x a b t s f g) = (term892 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080523 A B x a b t s f g) (@lem5080508 A B x a b t s f g)). Qed.
Lemma lem5080525 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term877 A B a b t s f g) = (term893 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080524 A B x a b t s f g)). Qed.
Lemma lem5080526 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080527 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term878 A B a b t s f g) = (term894 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080526 A) (@lem5080525 A B a b t s f g)). Qed.
Lemma lem5080528 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term640 A B a b t s f g) = (term894 A B a b t s f g).
Proof. exact (TRANS (@lem5080504 A B a b t s f g) (@lem5080527 A B a b t s f g)). Qed.
Lemma lem5080529 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term820 A B a b t s f g) = (term894 A B a b t s f g).
Proof. exact (TRANS (@lem5080478 A B a b t s f g) (@lem5080528 A B a b t s f g)). Qed.
Lemma lem5080530 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term643 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (eq_refl (term643 A B t b s a f g)). Qed.
Lemma lem5080531 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term821 A B a b t s f g) = (term895 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080530 A B t b s a f g) (@lem5080529 A B a b t s f g)). Qed.
Lemma lem5080533 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080534 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080533 A P Q). Qed.
Lemma lem5080535 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term896 A B a b t s f g) = (term897 A B a b t s f g).
Proof. exact (@lem5080534 A (term516 A B t b s a f g) (term893 A B a b t s f g)). Qed.
Lemma lem5080536 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term898 A B a b t s f g x) = (term892 A B x a b t s f g).
Proof. exact (eq_refl (term898 A B a b t s f g x)). Qed.
Lemma lem5080537 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term899 A B a b t s f g) = (term893 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080536 A B x a b t s f g)). Qed.
Lemma lem5080538 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080539 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term900 A B a b t s f g) = (term894 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080538 A) (@lem5080537 A B a b t s f g)). Qed.
Lemma lem5080540 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term643 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (eq_refl (term643 A B t b s a f g)). Qed.
Lemma lem5080541 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term896 A B a b t s f g) = (term895 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080540 A B t b s a f g) (@lem5080539 A B a b t s f g)). Qed.
Lemma lem5080542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080543 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term901 A B a b t s f g) = (term902 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080542) (@lem5080541 A B a b t s f g)). Qed.
Lemma lem5080544 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term898 A B a b t s f g x) = (term892 A B x a b t s f g).
Proof. exact (eq_refl (term898 A B a b t s f g x)). Qed.
Lemma lem5080545 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term643 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (eq_refl (term643 A B t b s a f g)). Qed.
Lemma lem5080546 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term903 A B a b t s f g x) = (term904 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080545 A B t b s a f g) (@lem5080544 A B x a b t s f g)). Qed.
Lemma lem5080547 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term905 A B a b t s f g) = (term906 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080546 A B x a b t s f g)). Qed.
Lemma lem5080548 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080549 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term897 A B a b t s f g) = (term907 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080548 A) (@lem5080547 A B a b t s f g)). Qed.
Lemma lem5080550 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term896 A B a b t s f g) = (term897 A B a b t s f g)) = ((term895 A B a b t s f g) = (term907 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080543 A B a b t s f g) (@lem5080549 A B a b t s f g)). Qed.
Lemma lem5080551 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term895 A B a b t s f g) = (term907 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080550 A B a b t s f g) (@lem5080535 A B a b t s f g)). Qed.
Lemma lem5080553 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080554 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080553 B P Q). Qed.
Lemma lem5080555 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term908 A B x a b t s f g) = (term909 A B x a b t s f g).
Proof. exact (@lem5080554 B (term516 A B t b s a f g) (term891 A B x a b t s f g)). Qed.
Lemma lem5080556 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term910 A B x a b t s f g y) = (term889 A B x a b t s f g y).
Proof. exact (eq_refl (term910 A B x a b t s f g y)). Qed.
Lemma lem5080557 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term911 A B x a b t s f g) = (term891 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080556 A B x a b t s f g y)). Qed.
Lemma lem5080558 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080559 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term912 A B x a b t s f g) = (term892 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080558 B) (@lem5080557 A B x a b t s f g)). Qed.
Lemma lem5080560 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term643 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (eq_refl (term643 A B t b s a f g)). Qed.
Lemma lem5080561 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term908 A B x a b t s f g) = (term904 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080560 A B t b s a f g) (@lem5080559 A B x a b t s f g)). Qed.
Lemma lem5080562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080563 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term913 A B x a b t s f g) = (term914 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080562) (@lem5080561 A B x a b t s f g)). Qed.
Lemma lem5080564 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term910 A B x a b t s f g y) = (term889 A B x a b t s f g y).
Proof. exact (eq_refl (term910 A B x a b t s f g y)). Qed.
Lemma lem5080565 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term643 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (eq_refl (term643 A B t b s a f g)). Qed.
Lemma lem5080566 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term915 A B x a b t s f g y) = (term916 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080565 A B t b s a f g) (@lem5080564 A B x a b t s f g y)). Qed.
Lemma lem5080567 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term917 A B x a b t s f g) = (term918 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080566 A B x a b t s f g y)). Qed.
Lemma lem5080568 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080569 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term909 A B x a b t s f g) = (term919 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080568 B) (@lem5080567 A B x a b t s f g)). Qed.
Lemma lem5080570 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term908 A B x a b t s f g) = (term909 A B x a b t s f g)) = ((term904 A B x a b t s f g) = (term919 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080563 A B x a b t s f g) (@lem5080569 A B x a b t s f g)). Qed.
Lemma lem5080571 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term904 A B x a b t s f g) = (term919 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080570 A B x a b t s f g) (@lem5080555 A B x a b t s f g)). Qed.
Lemma lem5080572 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term906 A B a b t s f g) = (term920 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080571 A B x a b t s f g)). Qed.
Lemma lem5080573 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080574 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term907 A B a b t s f g) = (term921 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080573 A) (@lem5080572 A B a b t s f g)). Qed.
Lemma lem5080575 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term895 A B a b t s f g) = (term921 A B a b t s f g).
Proof. exact (TRANS (@lem5080551 A B a b t s f g) (@lem5080574 A B a b t s f g)). Qed.
Lemma lem5080576 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term821 A B a b t s f g) = (term921 A B a b t s f g).
Proof. exact (TRANS (@lem5080531 A B a b t s f g) (@lem5080575 A B a b t s f g)). Qed.
Lemma lem5080577 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (eq_refl (term647 A B s a t b g f)). Qed.
Lemma lem5080578 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term822 A B a b t s f g) = (term922 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080577 A B s a t b g f) (@lem5080576 A B a b t s f g)). Qed.
Lemma lem5080580 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080581 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080580 A P Q). Qed.
Lemma lem5080582 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term923 A B a b t s f g) = (term924 A B a b t s f g).
Proof. exact (@lem5080581 A (term512 A B s a t b g f) (term920 A B a b t s f g)). Qed.
Lemma lem5080583 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term925 A B a b t s f g x) = (term919 A B x a b t s f g).
Proof. exact (eq_refl (term925 A B a b t s f g x)). Qed.
Lemma lem5080584 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term926 A B a b t s f g) = (term920 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080583 A B x a b t s f g)). Qed.
Lemma lem5080585 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080586 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term927 A B a b t s f g) = (term921 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080585 A) (@lem5080584 A B a b t s f g)). Qed.
Lemma lem5080587 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (eq_refl (term647 A B s a t b g f)). Qed.
Lemma lem5080588 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term923 A B a b t s f g) = (term922 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080587 A B s a t b g f) (@lem5080586 A B a b t s f g)). Qed.
Lemma lem5080589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080590 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term928 A B a b t s f g) = (term929 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080589) (@lem5080588 A B a b t s f g)). Qed.
Lemma lem5080591 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term925 A B a b t s f g x) = (term919 A B x a b t s f g).
Proof. exact (eq_refl (term925 A B a b t s f g x)). Qed.
Lemma lem5080592 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (eq_refl (term647 A B s a t b g f)). Qed.
Lemma lem5080593 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term930 A B a b t s f g x) = (term931 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080592 A B s a t b g f) (@lem5080591 A B x a b t s f g)). Qed.
Lemma lem5080594 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term932 A B a b t s f g) = (term933 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080593 A B x a b t s f g)). Qed.
Lemma lem5080595 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080596 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term924 A B a b t s f g) = (term934 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080595 A) (@lem5080594 A B a b t s f g)). Qed.
Lemma lem5080597 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term923 A B a b t s f g) = (term924 A B a b t s f g)) = ((term922 A B a b t s f g) = (term934 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080590 A B a b t s f g) (@lem5080596 A B a b t s f g)). Qed.
Lemma lem5080598 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term922 A B a b t s f g) = (term934 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080597 A B a b t s f g) (@lem5080582 A B a b t s f g)). Qed.
Lemma lem5080600 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080601 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080600 B P Q). Qed.
Lemma lem5080602 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term935 A B x a b t s f g) = (term936 A B x a b t s f g).
Proof. exact (@lem5080601 B (term512 A B s a t b g f) (term918 A B x a b t s f g)). Qed.
Lemma lem5080603 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term937 A B x a b t s f g y) = (term916 A B x a b t s f g y).
Proof. exact (eq_refl (term937 A B x a b t s f g y)). Qed.
Lemma lem5080604 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term938 A B x a b t s f g) = (term918 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080603 A B x a b t s f g y)). Qed.
Lemma lem5080605 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080606 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term939 A B x a b t s f g) = (term919 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080605 B) (@lem5080604 A B x a b t s f g)). Qed.
Lemma lem5080607 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (eq_refl (term647 A B s a t b g f)). Qed.
Lemma lem5080608 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term935 A B x a b t s f g) = (term931 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080607 A B s a t b g f) (@lem5080606 A B x a b t s f g)). Qed.
Lemma lem5080609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080610 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term940 A B x a b t s f g) = (term941 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080609) (@lem5080608 A B x a b t s f g)). Qed.
Lemma lem5080611 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term937 A B x a b t s f g y) = (term916 A B x a b t s f g y).
Proof. exact (eq_refl (term937 A B x a b t s f g y)). Qed.
Lemma lem5080612 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (eq_refl (term647 A B s a t b g f)). Qed.
Lemma lem5080613 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term942 A B x a b t s f g y) = (term943 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080612 A B s a t b g f) (@lem5080611 A B x a b t s f g y)). Qed.
Lemma lem5080614 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term944 A B x a b t s f g) = (term945 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080613 A B x a b t s f g y)). Qed.
Lemma lem5080615 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080616 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term936 A B x a b t s f g) = (term946 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080615 B) (@lem5080614 A B x a b t s f g)). Qed.
Lemma lem5080617 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term935 A B x a b t s f g) = (term936 A B x a b t s f g)) = ((term931 A B x a b t s f g) = (term946 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080610 A B x a b t s f g) (@lem5080616 A B x a b t s f g)). Qed.
Lemma lem5080618 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term931 A B x a b t s f g) = (term946 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080617 A B x a b t s f g) (@lem5080602 A B x a b t s f g)). Qed.
Lemma lem5080619 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term933 A B a b t s f g) = (term947 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080618 A B x a b t s f g)). Qed.
Lemma lem5080620 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080621 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term934 A B a b t s f g) = (term948 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080620 A) (@lem5080619 A B a b t s f g)). Qed.
Lemma lem5080622 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term922 A B a b t s f g) = (term948 A B a b t s f g).
Proof. exact (TRANS (@lem5080598 A B a b t s f g) (@lem5080621 A B a b t s f g)). Qed.
Lemma lem5080623 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term822 A B a b t s f g) = (term948 A B a b t s f g).
Proof. exact (TRANS (@lem5080578 A B a b t s f g) (@lem5080622 A B a b t s f g)). Qed.
Lemma lem5080624 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5080625 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term823 A B a b t s f g) = (term949 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080624 B b t) (@lem5080623 A B a b t s f g)). Qed.
Lemma lem5080627 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080628 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080627 A P Q). Qed.
Lemma lem5080629 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term950 A B a b t s f g) = (term951 A B a b t s f g).
Proof. exact (@lem5080628 A (@IN B b t) (term947 A B a b t s f g)). Qed.
Lemma lem5080630 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term952 A B a b t s f g x) = (term946 A B x a b t s f g).
Proof. exact (eq_refl (term952 A B a b t s f g x)). Qed.
Lemma lem5080631 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term953 A B a b t s f g) = (term947 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080630 A B x a b t s f g)). Qed.
Lemma lem5080632 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080633 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term954 A B a b t s f g) = (term948 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080632 A) (@lem5080631 A B a b t s f g)). Qed.
Lemma lem5080634 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5080635 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term950 A B a b t s f g) = (term949 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080634 B b t) (@lem5080633 A B a b t s f g)). Qed.
Lemma lem5080636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080637 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term955 A B a b t s f g) = (term956 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080636) (@lem5080635 A B a b t s f g)). Qed.
Lemma lem5080638 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term952 A B a b t s f g x) = (term946 A B x a b t s f g).
Proof. exact (eq_refl (term952 A B a b t s f g x)). Qed.
Lemma lem5080639 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5080640 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term957 A B a b t s f g x) = (term958 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080639 B b t) (@lem5080638 A B x a b t s f g)). Qed.
Lemma lem5080641 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term959 A B a b t s f g) = (term960 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080640 A B x a b t s f g)). Qed.
Lemma lem5080642 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080643 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term951 A B a b t s f g) = (term961 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080642 A) (@lem5080641 A B a b t s f g)). Qed.
Lemma lem5080644 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term950 A B a b t s f g) = (term951 A B a b t s f g)) = ((term949 A B a b t s f g) = (term961 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080637 A B a b t s f g) (@lem5080643 A B a b t s f g)). Qed.
Lemma lem5080645 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term949 A B a b t s f g) = (term961 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080644 A B a b t s f g) (@lem5080629 A B a b t s f g)). Qed.
Lemma lem5080647 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080648 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080647 B P Q). Qed.
Lemma lem5080649 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term962 A B x a b t s f g) = (term963 A B x a b t s f g).
Proof. exact (@lem5080648 B (@IN B b t) (term945 A B x a b t s f g)). Qed.
Lemma lem5080650 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term964 A B x a b t s f g y) = (term943 A B x a b t s f g y).
Proof. exact (eq_refl (term964 A B x a b t s f g y)). Qed.
Lemma lem5080651 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term965 A B x a b t s f g) = (term945 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080650 A B x a b t s f g y)). Qed.
Lemma lem5080652 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080653 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term966 A B x a b t s f g) = (term946 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080652 B) (@lem5080651 A B x a b t s f g)). Qed.
Lemma lem5080654 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5080655 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term962 A B x a b t s f g) = (term958 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080654 B b t) (@lem5080653 A B x a b t s f g)). Qed.
Lemma lem5080656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080657 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term967 A B x a b t s f g) = (term968 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080656) (@lem5080655 A B x a b t s f g)). Qed.
Lemma lem5080658 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term964 A B x a b t s f g y) = (term943 A B x a b t s f g y).
Proof. exact (eq_refl (term964 A B x a b t s f g y)). Qed.
Lemma lem5080659 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5080660 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term969 A B x a b t s f g y) = (term970 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080659 B b t) (@lem5080658 A B x a b t s f g y)). Qed.
Lemma lem5080661 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term971 A B x a b t s f g) = (term972 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080660 A B x a b t s f g y)). Qed.
Lemma lem5080662 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080663 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term963 A B x a b t s f g) = (term973 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080662 B) (@lem5080661 A B x a b t s f g)). Qed.
Lemma lem5080664 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term962 A B x a b t s f g) = (term963 A B x a b t s f g)) = ((term958 A B x a b t s f g) = (term973 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080657 A B x a b t s f g) (@lem5080663 A B x a b t s f g)). Qed.
Lemma lem5080665 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term958 A B x a b t s f g) = (term973 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080664 A B x a b t s f g) (@lem5080649 A B x a b t s f g)). Qed.
Lemma lem5080666 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term960 A B a b t s f g) = (term974 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080665 A B x a b t s f g)). Qed.
Lemma lem5080667 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080668 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term961 A B a b t s f g) = (term975 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080667 A) (@lem5080666 A B a b t s f g)). Qed.
Lemma lem5080669 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term949 A B a b t s f g) = (term975 A B a b t s f g).
Proof. exact (TRANS (@lem5080645 A B a b t s f g) (@lem5080668 A B a b t s f g)). Qed.
Lemma lem5080670 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term823 A B a b t s f g) = (term975 A B a b t s f g).
Proof. exact (TRANS (@lem5080625 A B a b t s f g) (@lem5080669 A B a b t s f g)). Qed.
Lemma lem5080671 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5080672 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term824 A B a b t s f g) = (term976 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080671 A a s) (@lem5080670 A B a b t s f g)). Qed.
Lemma lem5080674 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080675 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080674 A P Q). Qed.
Lemma lem5080676 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term977 A B a b t s f g) = (term978 A B a b t s f g).
Proof. exact (@lem5080675 A (@IN A a s) (term974 A B a b t s f g)). Qed.
Lemma lem5080677 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term979 A B a b t s f g x) = (term973 A B x a b t s f g).
Proof. exact (eq_refl (term979 A B a b t s f g x)). Qed.
Lemma lem5080678 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term980 A B a b t s f g) = (term974 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080677 A B x a b t s f g)). Qed.
Lemma lem5080679 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080680 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term981 A B a b t s f g) = (term975 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080679 A) (@lem5080678 A B a b t s f g)). Qed.
Lemma lem5080681 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5080682 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term977 A B a b t s f g) = (term976 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080681 A a s) (@lem5080680 A B a b t s f g)). Qed.
Lemma lem5080683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080684 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term982 A B a b t s f g) = (term983 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080683) (@lem5080682 A B a b t s f g)). Qed.
Lemma lem5080685 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term979 A B a b t s f g x) = (term973 A B x a b t s f g).
Proof. exact (eq_refl (term979 A B a b t s f g x)). Qed.
Lemma lem5080686 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5080687 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term984 A B a b t s f g x) = (term985 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080686 A a s) (@lem5080685 A B x a b t s f g)). Qed.
Lemma lem5080688 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term986 A B a b t s f g) = (term987 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080687 A B x a b t s f g)). Qed.
Lemma lem5080689 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080690 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term978 A B a b t s f g) = (term988 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080689 A) (@lem5080688 A B a b t s f g)). Qed.
Lemma lem5080691 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term977 A B a b t s f g) = (term978 A B a b t s f g)) = ((term976 A B a b t s f g) = (term988 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080684 A B a b t s f g) (@lem5080690 A B a b t s f g)). Qed.
Lemma lem5080692 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term976 A B a b t s f g) = (term988 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080691 A B a b t s f g) (@lem5080676 A B a b t s f g)). Qed.
Lemma lem5080694 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080695 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080694 B P Q). Qed.
Lemma lem5080696 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term989 A B x a b t s f g) = (term990 A B x a b t s f g).
Proof. exact (@lem5080695 B (@IN A a s) (term972 A B x a b t s f g)). Qed.
Lemma lem5080697 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term991 A B x a b t s f g y) = (term970 A B x a b t s f g y).
Proof. exact (eq_refl (term991 A B x a b t s f g y)). Qed.
Lemma lem5080698 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term992 A B x a b t s f g) = (term972 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080697 A B x a b t s f g y)). Qed.
Lemma lem5080699 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080700 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term993 A B x a b t s f g) = (term973 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080699 B) (@lem5080698 A B x a b t s f g)). Qed.
Lemma lem5080701 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5080702 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term989 A B x a b t s f g) = (term985 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080701 A a s) (@lem5080700 A B x a b t s f g)). Qed.
Lemma lem5080703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080704 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term994 A B x a b t s f g) = (term995 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080703) (@lem5080702 A B x a b t s f g)). Qed.
Lemma lem5080705 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term991 A B x a b t s f g y) = (term970 A B x a b t s f g y).
Proof. exact (eq_refl (term991 A B x a b t s f g y)). Qed.
Lemma lem5080706 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5080707 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term996 A B x a b t s f g y) = (term997 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080706 A a s) (@lem5080705 A B x a b t s f g y)). Qed.
Lemma lem5080708 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term998 A B x a b t s f g) = (term999 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080707 A B x a b t s f g y)). Qed.
Lemma lem5080709 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080710 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term990 A B x a b t s f g) = (term1000 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080709 B) (@lem5080708 A B x a b t s f g)). Qed.
Lemma lem5080711 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term989 A B x a b t s f g) = (term990 A B x a b t s f g)) = ((term985 A B x a b t s f g) = (term1000 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080704 A B x a b t s f g) (@lem5080710 A B x a b t s f g)). Qed.
Lemma lem5080712 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term985 A B x a b t s f g) = (term1000 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080711 A B x a b t s f g) (@lem5080696 A B x a b t s f g)). Qed.
Lemma lem5080713 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term987 A B a b t s f g) = (term1001 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080712 A B x a b t s f g)). Qed.
Lemma lem5080714 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080715 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term988 A B a b t s f g) = (term1002 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080714 A) (@lem5080713 A B a b t s f g)). Qed.
Lemma lem5080716 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term976 A B a b t s f g) = (term1002 A B a b t s f g).
Proof. exact (TRANS (@lem5080692 A B a b t s f g) (@lem5080715 A B a b t s f g)). Qed.
Lemma lem5080717 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term824 A B a b t s f g) = (term1002 A B a b t s f g).
Proof. exact (TRANS (@lem5080672 A B a b t s f g) (@lem5080716 A B a b t s f g)). Qed.
Lemma lem5080718 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5080719 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term825 A B a b t s f g) = (term1003 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080718 A B s t) (@lem5080717 A B a b t s f g)). Qed.
Lemma lem5080721 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080722 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080721 A P Q). Qed.
Lemma lem5080723 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1004 A B a b t s f g) = (term1005 A B a b t s f g).
Proof. exact (@lem5080722 A ((@CARD A s) = (@CARD B t)) (term1001 A B a b t s f g)). Qed.
Lemma lem5080724 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1006 A B a b t s f g x) = (term1000 A B x a b t s f g).
Proof. exact (eq_refl (term1006 A B a b t s f g x)). Qed.
Lemma lem5080725 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1007 A B a b t s f g) = (term1001 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080724 A B x a b t s f g)). Qed.
Lemma lem5080726 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080727 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1008 A B a b t s f g) = (term1002 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080726 A) (@lem5080725 A B a b t s f g)). Qed.
Lemma lem5080728 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5080729 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1004 A B a b t s f g) = (term1003 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080728 A B s t) (@lem5080727 A B a b t s f g)). Qed.
Lemma lem5080730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080731 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1009 A B a b t s f g) = (term1010 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080730) (@lem5080729 A B a b t s f g)). Qed.
Lemma lem5080732 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1006 A B a b t s f g x) = (term1000 A B x a b t s f g).
Proof. exact (eq_refl (term1006 A B a b t s f g x)). Qed.
Lemma lem5080733 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5080734 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1011 A B a b t s f g x) = (term1012 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080733 A B s t) (@lem5080732 A B x a b t s f g)). Qed.
Lemma lem5080735 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1013 A B a b t s f g) = (term1014 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080734 A B x a b t s f g)). Qed.
Lemma lem5080736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080737 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1005 A B a b t s f g) = (term1015 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080736 A) (@lem5080735 A B a b t s f g)). Qed.
Lemma lem5080738 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1004 A B a b t s f g) = (term1005 A B a b t s f g)) = ((term1003 A B a b t s f g) = (term1015 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080731 A B a b t s f g) (@lem5080737 A B a b t s f g)). Qed.
Lemma lem5080739 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1003 A B a b t s f g) = (term1015 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080738 A B a b t s f g) (@lem5080723 A B a b t s f g)). Qed.
Lemma lem5080741 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080742 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080741 B P Q). Qed.
Lemma lem5080743 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1016 A B x a b t s f g) = (term1017 A B x a b t s f g).
Proof. exact (@lem5080742 B ((@CARD A s) = (@CARD B t)) (term999 A B x a b t s f g)). Qed.
Lemma lem5080744 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1018 A B x a b t s f g y) = (term997 A B x a b t s f g y).
Proof. exact (eq_refl (term1018 A B x a b t s f g y)). Qed.
Lemma lem5080745 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1019 A B x a b t s f g) = (term999 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080744 A B x a b t s f g y)). Qed.
Lemma lem5080746 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080747 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1020 A B x a b t s f g) = (term1000 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080746 B) (@lem5080745 A B x a b t s f g)). Qed.
Lemma lem5080748 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5080749 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1016 A B x a b t s f g) = (term1012 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080748 A B s t) (@lem5080747 A B x a b t s f g)). Qed.
Lemma lem5080750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080751 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1021 A B x a b t s f g) = (term1022 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080750) (@lem5080749 A B x a b t s f g)). Qed.
Lemma lem5080752 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1018 A B x a b t s f g y) = (term997 A B x a b t s f g y).
Proof. exact (eq_refl (term1018 A B x a b t s f g y)). Qed.
Lemma lem5080753 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5080754 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1023 A B x a b t s f g y) = (term1024 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080753 A B s t) (@lem5080752 A B x a b t s f g y)). Qed.
Lemma lem5080755 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1025 A B x a b t s f g) = (term1026 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080754 A B x a b t s f g y)). Qed.
Lemma lem5080756 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080757 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1017 A B x a b t s f g) = (term1027 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080756 B) (@lem5080755 A B x a b t s f g)). Qed.
Lemma lem5080758 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1016 A B x a b t s f g) = (term1017 A B x a b t s f g)) = ((term1012 A B x a b t s f g) = (term1027 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080751 A B x a b t s f g) (@lem5080757 A B x a b t s f g)). Qed.
Lemma lem5080759 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1012 A B x a b t s f g) = (term1027 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080758 A B x a b t s f g) (@lem5080743 A B x a b t s f g)). Qed.
Lemma lem5080760 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1014 A B a b t s f g) = (term1028 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080759 A B x a b t s f g)). Qed.
Lemma lem5080761 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080762 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1015 A B a b t s f g) = (term1029 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080761 A) (@lem5080760 A B a b t s f g)). Qed.
Lemma lem5080763 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1003 A B a b t s f g) = (term1029 A B a b t s f g).
Proof. exact (TRANS (@lem5080739 A B a b t s f g) (@lem5080762 A B a b t s f g)). Qed.
Lemma lem5080764 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term825 A B a b t s f g) = (term1029 A B a b t s f g).
Proof. exact (TRANS (@lem5080719 A B a b t s f g) (@lem5080763 A B a b t s f g)). Qed.
Lemma lem5080765 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5080766 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term826 A B a b t s f g) = (term1030 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080765 B t) (@lem5080764 A B a b t s f g)). Qed.
Lemma lem5080768 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080769 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080768 A P Q). Qed.
Lemma lem5080770 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1031 A B a b t s f g) = (term1032 A B a b t s f g).
Proof. exact (@lem5080769 A (@FINITE B t) (term1028 A B a b t s f g)). Qed.
Lemma lem5080771 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1033 A B a b t s f g x) = (term1027 A B x a b t s f g).
Proof. exact (eq_refl (term1033 A B a b t s f g x)). Qed.
Lemma lem5080772 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1034 A B a b t s f g) = (term1028 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080771 A B x a b t s f g)). Qed.
Lemma lem5080773 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080774 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1035 A B a b t s f g) = (term1029 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080773 A) (@lem5080772 A B a b t s f g)). Qed.
Lemma lem5080775 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5080776 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1031 A B a b t s f g) = (term1030 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080775 B t) (@lem5080774 A B a b t s f g)). Qed.
Lemma lem5080777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080778 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1036 A B a b t s f g) = (term1037 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080777) (@lem5080776 A B a b t s f g)). Qed.
Lemma lem5080779 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1033 A B a b t s f g x) = (term1027 A B x a b t s f g).
Proof. exact (eq_refl (term1033 A B a b t s f g x)). Qed.
Lemma lem5080780 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5080781 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1038 A B a b t s f g x) = (term1039 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080780 B t) (@lem5080779 A B x a b t s f g)). Qed.
Lemma lem5080782 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1040 A B a b t s f g) = (term1041 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080781 A B x a b t s f g)). Qed.
Lemma lem5080783 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080784 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1032 A B a b t s f g) = (term1042 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080783 A) (@lem5080782 A B a b t s f g)). Qed.
Lemma lem5080785 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1031 A B a b t s f g) = (term1032 A B a b t s f g)) = ((term1030 A B a b t s f g) = (term1042 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080778 A B a b t s f g) (@lem5080784 A B a b t s f g)). Qed.
Lemma lem5080786 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1030 A B a b t s f g) = (term1042 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080785 A B a b t s f g) (@lem5080770 A B a b t s f g)). Qed.
Lemma lem5080788 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080789 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080788 B P Q). Qed.
Lemma lem5080790 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1043 A B x a b t s f g) = (term1044 A B x a b t s f g).
Proof. exact (@lem5080789 B (@FINITE B t) (term1026 A B x a b t s f g)). Qed.
Lemma lem5080791 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1045 A B x a b t s f g y) = (term1024 A B x a b t s f g y).
Proof. exact (eq_refl (term1045 A B x a b t s f g y)). Qed.
Lemma lem5080792 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1046 A B x a b t s f g) = (term1026 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080791 A B x a b t s f g y)). Qed.
Lemma lem5080793 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080794 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1047 A B x a b t s f g) = (term1027 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080793 B) (@lem5080792 A B x a b t s f g)). Qed.
Lemma lem5080795 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5080796 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1043 A B x a b t s f g) = (term1039 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080795 B t) (@lem5080794 A B x a b t s f g)). Qed.
Lemma lem5080797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080798 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1048 A B x a b t s f g) = (term1049 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080797) (@lem5080796 A B x a b t s f g)). Qed.
Lemma lem5080799 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1045 A B x a b t s f g y) = (term1024 A B x a b t s f g y).
Proof. exact (eq_refl (term1045 A B x a b t s f g y)). Qed.
Lemma lem5080800 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5080801 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1050 A B x a b t s f g y) = (term1051 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080800 B t) (@lem5080799 A B x a b t s f g y)). Qed.
Lemma lem5080802 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1052 A B x a b t s f g) = (term1053 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080801 A B x a b t s f g y)). Qed.
Lemma lem5080803 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080804 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1044 A B x a b t s f g) = (term1054 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080803 B) (@lem5080802 A B x a b t s f g)). Qed.
Lemma lem5080805 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1043 A B x a b t s f g) = (term1044 A B x a b t s f g)) = ((term1039 A B x a b t s f g) = (term1054 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080798 A B x a b t s f g) (@lem5080804 A B x a b t s f g)). Qed.
Lemma lem5080806 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1039 A B x a b t s f g) = (term1054 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080805 A B x a b t s f g) (@lem5080790 A B x a b t s f g)). Qed.
Lemma lem5080807 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1041 A B a b t s f g) = (term1055 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080806 A B x a b t s f g)). Qed.
Lemma lem5080808 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080809 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1042 A B a b t s f g) = (term1056 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080808 A) (@lem5080807 A B a b t s f g)). Qed.
Lemma lem5080810 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1030 A B a b t s f g) = (term1056 A B a b t s f g).
Proof. exact (TRANS (@lem5080786 A B a b t s f g) (@lem5080809 A B a b t s f g)). Qed.
Lemma lem5080811 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term826 A B a b t s f g) = (term1056 A B a b t s f g).
Proof. exact (TRANS (@lem5080766 A B a b t s f g) (@lem5080810 A B a b t s f g)). Qed.
Lemma lem5080812 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term827 A B a b s f g) = (term1057 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080811 A B a b t s f g)). Qed.
Lemma lem5080813 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080814 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term828 A B a b s f g) = (term1058 A B a b s f g).
Proof. exact (MK_COMB (@lem5080813 B) (@lem5080812 A B a b s f g)). Qed.
Lemma lem5080815 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080816 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term829 A B a b s f g) = (term1059 A B a b s f g).
Proof. exact (MK_COMB (@lem5080815 A s) (@lem5080814 A B a b s f g)). Qed.
Lemma lem5080818 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080819 {B : Type'} (P : Prop) (Q : type686 B) : (term764 B P Q) = (term763 B P Q).
Proof. exact (@lem5080818 (B -> Prop) P Q). Qed.
Lemma lem5080820 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1060 A B a b s f g) = (term1061 A B a b s f g).
Proof. exact (@lem5080819 B (@FINITE A s) (term1057 A B a b s f g)). Qed.
Lemma lem5080821 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1062 A B a b s f g t) = (term1056 A B a b t s f g).
Proof. exact (eq_refl (term1062 A B a b s f g t)). Qed.
Lemma lem5080822 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1063 A B a b s f g) = (term1057 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080821 A B a b t s f g)). Qed.
Lemma lem5080823 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080824 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1064 A B a b s f g) = (term1058 A B a b s f g).
Proof. exact (MK_COMB (@lem5080823 B) (@lem5080822 A B a b s f g)). Qed.
Lemma lem5080825 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080826 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1060 A B a b s f g) = (term1059 A B a b s f g).
Proof. exact (MK_COMB (@lem5080825 A s) (@lem5080824 A B a b s f g)). Qed.
Lemma lem5080827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080828 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1065 A B a b s f g) = (term1066 A B a b s f g).
Proof. exact (MK_COMB (@lem5080827) (@lem5080826 A B a b s f g)). Qed.
Lemma lem5080829 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1062 A B a b s f g t) = (term1056 A B a b t s f g).
Proof. exact (eq_refl (term1062 A B a b s f g t)). Qed.
Lemma lem5080830 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080831 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1067 A B a b s f g t) = (term1068 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080830 A s) (@lem5080829 A B a b t s f g)). Qed.
Lemma lem5080832 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1069 A B a b s f g) = (term1070 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080831 A B a b t s f g)). Qed.
Lemma lem5080833 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080834 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1061 A B a b s f g) = (term1071 A B a b s f g).
Proof. exact (MK_COMB (@lem5080833 B) (@lem5080832 A B a b s f g)). Qed.
Lemma lem5080835 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1060 A B a b s f g) = (term1061 A B a b s f g)) = ((term1059 A B a b s f g) = (term1071 A B a b s f g)).
Proof. exact (MK_COMB (@lem5080828 A B a b s f g) (@lem5080834 A B a b s f g)). Qed.
Lemma lem5080836 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1059 A B a b s f g) = (term1071 A B a b s f g).
Proof. exact (EQ_MP (@lem5080835 A B a b s f g) (@lem5080820 A B a b s f g)). Qed.
Lemma lem5080838 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080839 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080838 A P Q). Qed.
Lemma lem5080840 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1072 A B a b t s f g) = (term1073 A B a b t s f g).
Proof. exact (@lem5080839 A (@FINITE A s) (term1055 A B a b t s f g)). Qed.
Lemma lem5080841 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1074 A B a b t s f g x) = (term1054 A B x a b t s f g).
Proof. exact (eq_refl (term1074 A B a b t s f g x)). Qed.
Lemma lem5080842 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1075 A B a b t s f g) = (term1055 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080841 A B x a b t s f g)). Qed.
Lemma lem5080843 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080844 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1076 A B a b t s f g) = (term1056 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080843 A) (@lem5080842 A B a b t s f g)). Qed.
Lemma lem5080845 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080846 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1072 A B a b t s f g) = (term1068 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080845 A s) (@lem5080844 A B a b t s f g)). Qed.
Lemma lem5080847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080848 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1077 A B a b t s f g) = (term1078 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080847) (@lem5080846 A B a b t s f g)). Qed.
Lemma lem5080849 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1074 A B a b t s f g x) = (term1054 A B x a b t s f g).
Proof. exact (eq_refl (term1074 A B a b t s f g x)). Qed.
Lemma lem5080850 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080851 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1079 A B a b t s f g x) = (term1080 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080850 A s) (@lem5080849 A B x a b t s f g)). Qed.
Lemma lem5080852 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1081 A B a b t s f g) = (term1082 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080851 A B x a b t s f g)). Qed.
Lemma lem5080853 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080854 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1073 A B a b t s f g) = (term1083 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080853 A) (@lem5080852 A B a b t s f g)). Qed.
Lemma lem5080855 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1072 A B a b t s f g) = (term1073 A B a b t s f g)) = ((term1068 A B a b t s f g) = (term1083 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080848 A B a b t s f g) (@lem5080854 A B a b t s f g)). Qed.
Lemma lem5080856 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1068 A B a b t s f g) = (term1083 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080855 A B a b t s f g) (@lem5080840 A B a b t s f g)). Qed.
Lemma lem5080858 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080859 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080858 B P Q). Qed.
Lemma lem5080860 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1084 A B x a b t s f g) = (term1085 A B x a b t s f g).
Proof. exact (@lem5080859 B (@FINITE A s) (term1053 A B x a b t s f g)). Qed.
Lemma lem5080861 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1086 A B x a b t s f g y) = (term1051 A B x a b t s f g y).
Proof. exact (eq_refl (term1086 A B x a b t s f g y)). Qed.
Lemma lem5080862 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1087 A B x a b t s f g) = (term1053 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080861 A B x a b t s f g y)). Qed.
Lemma lem5080863 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080864 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1088 A B x a b t s f g) = (term1054 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080863 B) (@lem5080862 A B x a b t s f g)). Qed.
Lemma lem5080865 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080866 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1084 A B x a b t s f g) = (term1080 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080865 A s) (@lem5080864 A B x a b t s f g)). Qed.
Lemma lem5080867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080868 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1089 A B x a b t s f g) = (term1090 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080867) (@lem5080866 A B x a b t s f g)). Qed.
Lemma lem5080869 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1086 A B x a b t s f g y) = (term1051 A B x a b t s f g y).
Proof. exact (eq_refl (term1086 A B x a b t s f g y)). Qed.
Lemma lem5080870 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5080871 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1091 A B x a b t s f g y) = (term1092 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5080870 A s) (@lem5080869 A B x a b t s f g y)). Qed.
Lemma lem5080872 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1093 A B x a b t s f g) = (term1094 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5080871 A B x a b t s f g y)). Qed.
Lemma lem5080873 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080874 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1085 A B x a b t s f g) = (term1095 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080873 B) (@lem5080872 A B x a b t s f g)). Qed.
Lemma lem5080875 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1084 A B x a b t s f g) = (term1085 A B x a b t s f g)) = ((term1080 A B x a b t s f g) = (term1095 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5080868 A B x a b t s f g) (@lem5080874 A B x a b t s f g)). Qed.
Lemma lem5080876 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1080 A B x a b t s f g) = (term1095 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5080875 A B x a b t s f g) (@lem5080860 A B x a b t s f g)). Qed.
Lemma lem5080877 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1082 A B a b t s f g) = (term1096 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080876 A B x a b t s f g)). Qed.
Lemma lem5080878 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080879 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1083 A B a b t s f g) = (term1097 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080878 A) (@lem5080877 A B a b t s f g)). Qed.
Lemma lem5080880 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1068 A B a b t s f g) = (term1097 A B a b t s f g).
Proof. exact (TRANS (@lem5080856 A B a b t s f g) (@lem5080879 A B a b t s f g)). Qed.
Lemma lem5080881 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1070 A B a b s f g) = (term1098 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080880 A B a b t s f g)). Qed.
Lemma lem5080882 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080883 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1071 A B a b s f g) = (term1099 A B a b s f g).
Proof. exact (MK_COMB (@lem5080882 B) (@lem5080881 A B a b s f g)). Qed.
Lemma lem5080884 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1059 A B a b s f g) = (term1099 A B a b s f g).
Proof. exact (TRANS (@lem5080836 A B a b s f g) (@lem5080883 A B a b s f g)). Qed.
Lemma lem5080885 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term829 A B a b s f g) = (term1099 A B a b s f g).
Proof. exact (TRANS (@lem5080816 A B a b s f g) (@lem5080884 A B a b s f g)). Qed.
Lemma lem5080886 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term830 A B a b f g) = (term1100 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5080885 A B a b s f g)). Qed.
Lemma lem5080887 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5080888 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term831 A B a b f g) = (term1101 A B a b f g).
Proof. exact (MK_COMB (@lem5080887 A) (@lem5080886 A B a b f g)). Qed.
Lemma lem5080889 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term832 A B a b g) = (term1102 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5080888 A B a b f g)). Qed.
Lemma lem5080890 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5080891 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term833 A B a b g) = (term1103 A B a b g).
Proof. exact (MK_COMB (@lem5080890 A B) (@lem5080889 A B a b g)). Qed.
Lemma lem5080892 {A B : Type'} (a : A) (g : B -> A) : (term834 A B a g) = (term1104 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5080891 A B a b g)). Qed.
Lemma lem5080893 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080894 {A B : Type'} (a : A) (g : B -> A) : (term835 A B a g) = (term1105 A B a g).
Proof. exact (MK_COMB (@lem5080893 B) (@lem5080892 A B a g)). Qed.
Lemma lem5080895 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080896 {A B : Type'} (a : A) (g : B -> A) : (term836 A B a g) = (term1106 A B a g).
Proof. exact (MK_COMB (@lem5080895 A a) (@lem5080894 A B a g)). Qed.
Lemma lem5080898 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080899 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080898 B P Q). Qed.
Lemma lem5080900 {A B : Type'} (a : A) (g : B -> A) : (term1107 A B a g) = (term1108 A B a g).
Proof. exact (@lem5080899 B (a = a) (term1104 A B a g)). Qed.
Lemma lem5080901 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1109 A B a g b) = (term1103 A B a b g).
Proof. exact (eq_refl (term1109 A B a g b)). Qed.
Lemma lem5080902 {A B : Type'} (a : A) (g : B -> A) : (term1110 A B a g) = (term1104 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5080901 A B a b g)). Qed.
Lemma lem5080903 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080904 {A B : Type'} (a : A) (g : B -> A) : (term1111 A B a g) = (term1105 A B a g).
Proof. exact (MK_COMB (@lem5080903 B) (@lem5080902 A B a g)). Qed.
Lemma lem5080905 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080906 {A B : Type'} (a : A) (g : B -> A) : (term1107 A B a g) = (term1106 A B a g).
Proof. exact (MK_COMB (@lem5080905 A a) (@lem5080904 A B a g)). Qed.
Lemma lem5080907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080908 {A B : Type'} (a : A) (g : B -> A) : (term1112 A B a g) = (term1113 A B a g).
Proof. exact (MK_COMB (@lem5080907) (@lem5080906 A B a g)). Qed.
Lemma lem5080909 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1109 A B a g b) = (term1103 A B a b g).
Proof. exact (eq_refl (term1109 A B a g b)). Qed.
Lemma lem5080910 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080911 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1114 A B a g b) = (term1115 A B a b g).
Proof. exact (MK_COMB (@lem5080910 A a) (@lem5080909 A B a b g)). Qed.
Lemma lem5080912 {A B : Type'} (a : A) (g : B -> A) : (term1116 A B a g) = (term1117 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5080911 A B a b g)). Qed.
Lemma lem5080913 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5080914 {A B : Type'} (a : A) (g : B -> A) : (term1108 A B a g) = (term1118 A B a g).
Proof. exact (MK_COMB (@lem5080913 B) (@lem5080912 A B a g)). Qed.
Lemma lem5080915 {A B : Type'} (a : A) (g : B -> A) : ((term1107 A B a g) = (term1108 A B a g)) = ((term1106 A B a g) = (term1118 A B a g)).
Proof. exact (MK_COMB (@lem5080908 A B a g) (@lem5080914 A B a g)). Qed.
Lemma lem5080916 {A B : Type'} (a : A) (g : B -> A) : (term1106 A B a g) = (term1118 A B a g).
Proof. exact (EQ_MP (@lem5080915 A B a g) (@lem5080900 A B a g)). Qed.
Lemma lem5080918 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080919 {A B : Type'} (P : Prop) (Q : type572 A B) : (term1119 A B P Q) = (term1120 A B P Q).
Proof. exact (@lem5080918 (A -> B) P Q). Qed.
Lemma lem5080920 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1121 A B a b g) = (term1122 A B a b g).
Proof. exact (@lem5080919 A B (a = a) (term1102 A B a b g)). Qed.
Lemma lem5080921 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1123 A B a b g f) = (term1101 A B a b f g).
Proof. exact (eq_refl (term1123 A B a b g f)). Qed.
Lemma lem5080922 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1124 A B a b g) = (term1102 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5080921 A B a b f g)). Qed.
Lemma lem5080923 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5080924 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1125 A B a b g) = (term1103 A B a b g).
Proof. exact (MK_COMB (@lem5080923 A B) (@lem5080922 A B a b g)). Qed.
Lemma lem5080925 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080926 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1121 A B a b g) = (term1115 A B a b g).
Proof. exact (MK_COMB (@lem5080925 A a) (@lem5080924 A B a b g)). Qed.
Lemma lem5080927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080928 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1126 A B a b g) = (term1127 A B a b g).
Proof. exact (MK_COMB (@lem5080927) (@lem5080926 A B a b g)). Qed.
Lemma lem5080929 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1123 A B a b g f) = (term1101 A B a b f g).
Proof. exact (eq_refl (term1123 A B a b g f)). Qed.
Lemma lem5080930 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080931 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1128 A B a b g f) = (term1129 A B a b f g).
Proof. exact (MK_COMB (@lem5080930 A a) (@lem5080929 A B a b f g)). Qed.
Lemma lem5080932 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1130 A B a b g) = (term1131 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5080931 A B a b f g)). Qed.
Lemma lem5080933 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5080934 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1122 A B a b g) = (term1132 A B a b g).
Proof. exact (MK_COMB (@lem5080933 A B) (@lem5080932 A B a b g)). Qed.
Lemma lem5080935 {A B : Type'} (a : A) (b : B) (g : B -> A) : ((term1121 A B a b g) = (term1122 A B a b g)) = ((term1115 A B a b g) = (term1132 A B a b g)).
Proof. exact (MK_COMB (@lem5080928 A B a b g) (@lem5080934 A B a b g)). Qed.
Lemma lem5080936 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1115 A B a b g) = (term1132 A B a b g).
Proof. exact (EQ_MP (@lem5080935 A B a b g) (@lem5080920 A B a b g)). Qed.
Lemma lem5080938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080939 {A : Type'} (P : Prop) (Q : type686 A) : (term764 A P Q) = (term763 A P Q).
Proof. exact (@lem5080938 (A -> Prop) P Q). Qed.
Lemma lem5080940 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1133 A B a b f g) = (term1134 A B a b f g).
Proof. exact (@lem5080939 A (a = a) (term1100 A B a b f g)). Qed.
Lemma lem5080941 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1135 A B a b f g s) = (term1099 A B a b s f g).
Proof. exact (eq_refl (term1135 A B a b f g s)). Qed.
Lemma lem5080942 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1136 A B a b f g) = (term1100 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5080941 A B a b s f g)). Qed.
Lemma lem5080943 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5080944 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1137 A B a b f g) = (term1101 A B a b f g).
Proof. exact (MK_COMB (@lem5080943 A) (@lem5080942 A B a b f g)). Qed.
Lemma lem5080945 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080946 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1133 A B a b f g) = (term1129 A B a b f g).
Proof. exact (MK_COMB (@lem5080945 A a) (@lem5080944 A B a b f g)). Qed.
Lemma lem5080947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080948 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1138 A B a b f g) = (term1139 A B a b f g).
Proof. exact (MK_COMB (@lem5080947) (@lem5080946 A B a b f g)). Qed.
Lemma lem5080949 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1135 A B a b f g s) = (term1099 A B a b s f g).
Proof. exact (eq_refl (term1135 A B a b f g s)). Qed.
Lemma lem5080950 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080951 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1140 A B a b f g s) = (term1141 A B a b s f g).
Proof. exact (MK_COMB (@lem5080950 A a) (@lem5080949 A B a b s f g)). Qed.
Lemma lem5080952 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1142 A B a b f g) = (term1143 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5080951 A B a b s f g)). Qed.
Lemma lem5080953 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5080954 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1134 A B a b f g) = (term1144 A B a b f g).
Proof. exact (MK_COMB (@lem5080953 A) (@lem5080952 A B a b f g)). Qed.
Lemma lem5080955 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : ((term1133 A B a b f g) = (term1134 A B a b f g)) = ((term1129 A B a b f g) = (term1144 A B a b f g)).
Proof. exact (MK_COMB (@lem5080948 A B a b f g) (@lem5080954 A B a b f g)). Qed.
Lemma lem5080956 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1129 A B a b f g) = (term1144 A B a b f g).
Proof. exact (EQ_MP (@lem5080955 A B a b f g) (@lem5080940 A B a b f g)). Qed.
Lemma lem5080958 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080959 {B : Type'} (P : Prop) (Q : type686 B) : (term764 B P Q) = (term763 B P Q).
Proof. exact (@lem5080958 (B -> Prop) P Q). Qed.
Lemma lem5080960 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1145 A B a b s f g) = (term1146 A B a b s f g).
Proof. exact (@lem5080959 B (a = a) (term1098 A B a b s f g)). Qed.
Lemma lem5080961 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1147 A B a b s f g t) = (term1097 A B a b t s f g).
Proof. exact (eq_refl (term1147 A B a b s f g t)). Qed.
Lemma lem5080962 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1148 A B a b s f g) = (term1098 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080961 A B a b t s f g)). Qed.
Lemma lem5080963 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080964 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1149 A B a b s f g) = (term1099 A B a b s f g).
Proof. exact (MK_COMB (@lem5080963 B) (@lem5080962 A B a b s f g)). Qed.
Lemma lem5080965 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080966 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1145 A B a b s f g) = (term1141 A B a b s f g).
Proof. exact (MK_COMB (@lem5080965 A a) (@lem5080964 A B a b s f g)). Qed.
Lemma lem5080967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080968 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1150 A B a b s f g) = (term1151 A B a b s f g).
Proof. exact (MK_COMB (@lem5080967) (@lem5080966 A B a b s f g)). Qed.
Lemma lem5080969 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1147 A B a b s f g t) = (term1097 A B a b t s f g).
Proof. exact (eq_refl (term1147 A B a b s f g t)). Qed.
Lemma lem5080970 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080971 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1152 A B a b s f g t) = (term1153 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080970 A a) (@lem5080969 A B a b t s f g)). Qed.
Lemma lem5080972 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1154 A B a b s f g) = (term1155 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5080971 A B a b t s f g)). Qed.
Lemma lem5080973 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5080974 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1146 A B a b s f g) = (term1156 A B a b s f g).
Proof. exact (MK_COMB (@lem5080973 B) (@lem5080972 A B a b s f g)). Qed.
Lemma lem5080975 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1145 A B a b s f g) = (term1146 A B a b s f g)) = ((term1141 A B a b s f g) = (term1156 A B a b s f g)).
Proof. exact (MK_COMB (@lem5080968 A B a b s f g) (@lem5080974 A B a b s f g)). Qed.
Lemma lem5080976 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1141 A B a b s f g) = (term1156 A B a b s f g).
Proof. exact (EQ_MP (@lem5080975 A B a b s f g) (@lem5080960 A B a b s f g)). Qed.
Lemma lem5080978 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080979 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (@lem5080978 A P Q). Qed.
Lemma lem5080980 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1157 A B a b t s f g) = (term1158 A B a b t s f g).
Proof. exact (@lem5080979 A (a = a) (term1096 A B a b t s f g)). Qed.
Lemma lem5080981 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1159 A B a b t s f g x) = (term1095 A B x a b t s f g).
Proof. exact (eq_refl (term1159 A B a b t s f g x)). Qed.
Lemma lem5080982 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1160 A B a b t s f g) = (term1096 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080981 A B x a b t s f g)). Qed.
Lemma lem5080983 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080984 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1161 A B a b t s f g) = (term1097 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080983 A) (@lem5080982 A B a b t s f g)). Qed.
Lemma lem5080985 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080986 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1157 A B a b t s f g) = (term1153 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080985 A a) (@lem5080984 A B a b t s f g)). Qed.
Lemma lem5080987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5080988 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1162 A B a b t s f g) = (term1163 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080987) (@lem5080986 A B a b t s f g)). Qed.
Lemma lem5080989 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1159 A B a b t s f g x) = (term1095 A B x a b t s f g).
Proof. exact (eq_refl (term1159 A B a b t s f g x)). Qed.
Lemma lem5080990 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5080991 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1164 A B a b t s f g x) = (term1165 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5080990 A a) (@lem5080989 A B x a b t s f g)). Qed.
Lemma lem5080992 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1166 A B a b t s f g) = (term1167 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5080991 A B x a b t s f g)). Qed.
Lemma lem5080993 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5080994 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1158 A B a b t s f g) = (term1168 A B a b t s f g).
Proof. exact (MK_COMB (@lem5080993 A) (@lem5080992 A B a b t s f g)). Qed.
Lemma lem5080995 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1157 A B a b t s f g) = (term1158 A B a b t s f g)) = ((term1153 A B a b t s f g) = (term1168 A B a b t s f g)).
Proof. exact (MK_COMB (@lem5080988 A B a b t s f g) (@lem5080994 A B a b t s f g)). Qed.
Lemma lem5080996 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1153 A B a b t s f g) = (term1168 A B a b t s f g).
Proof. exact (EQ_MP (@lem5080995 A B a b t s f g) (@lem5080980 A B a b t s f g)). Qed.
Lemma lem5080998 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5080999 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5080998 B P Q). Qed.
Lemma lem5081000 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1169 A B x a b t s f g) = (term1170 A B x a b t s f g).
Proof. exact (@lem5080999 B (a = a) (term1094 A B x a b t s f g)). Qed.
Lemma lem5081001 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1171 A B x a b t s f g y) = (term1092 A B x a b t s f g y).
Proof. exact (eq_refl (term1171 A B x a b t s f g y)). Qed.
Lemma lem5081002 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1172 A B x a b t s f g) = (term1094 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5081001 A B x a b t s f g y)). Qed.
Lemma lem5081003 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081004 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1173 A B x a b t s f g) = (term1095 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5081003 B) (@lem5081002 A B x a b t s f g)). Qed.
Lemma lem5081005 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5081006 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1169 A B x a b t s f g) = (term1165 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5081005 A a) (@lem5081004 A B x a b t s f g)). Qed.
Lemma lem5081007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081008 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1174 A B x a b t s f g) = (term1175 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5081007) (@lem5081006 A B x a b t s f g)). Qed.
Lemma lem5081009 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1171 A B x a b t s f g y) = (term1092 A B x a b t s f g y).
Proof. exact (eq_refl (term1171 A B x a b t s f g y)). Qed.
Lemma lem5081010 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5081011 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1176 A B x a b t s f g y) = (term1177 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5081010 A a) (@lem5081009 A B x a b t s f g y)). Qed.
Lemma lem5081012 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1178 A B x a b t s f g) = (term1179 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5081011 A B x a b t s f g y)). Qed.
Lemma lem5081013 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081014 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1170 A B x a b t s f g) = (term1180 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5081013 B) (@lem5081012 A B x a b t s f g)). Qed.
Lemma lem5081015 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term1169 A B x a b t s f g) = (term1170 A B x a b t s f g)) = ((term1165 A B x a b t s f g) = (term1180 A B x a b t s f g)).
Proof. exact (MK_COMB (@lem5081008 A B x a b t s f g) (@lem5081014 A B x a b t s f g)). Qed.
Lemma lem5081016 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1165 A B x a b t s f g) = (term1180 A B x a b t s f g).
Proof. exact (EQ_MP (@lem5081015 A B x a b t s f g) (@lem5081000 A B x a b t s f g)). Qed.
Lemma lem5081017 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1167 A B a b t s f g) = (term1181 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5081016 A B x a b t s f g)). Qed.
Lemma lem5081018 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5081019 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1168 A B a b t s f g) = (term1182 A B a b t s f g).
Proof. exact (MK_COMB (@lem5081018 A) (@lem5081017 A B a b t s f g)). Qed.
Lemma lem5081020 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1153 A B a b t s f g) = (term1182 A B a b t s f g).
Proof. exact (TRANS (@lem5080996 A B a b t s f g) (@lem5081019 A B a b t s f g)). Qed.
Lemma lem5081021 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1155 A B a b s f g) = (term1183 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081020 A B a b t s f g)). Qed.
Lemma lem5081022 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081023 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1156 A B a b s f g) = (term1184 A B a b s f g).
Proof. exact (MK_COMB (@lem5081022 B) (@lem5081021 A B a b s f g)). Qed.
Lemma lem5081024 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1141 A B a b s f g) = (term1184 A B a b s f g).
Proof. exact (TRANS (@lem5080976 A B a b s f g) (@lem5081023 A B a b s f g)). Qed.
Lemma lem5081025 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1143 A B a b f g) = (term1185 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081024 A B a b s f g)). Qed.
Lemma lem5081026 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081027 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1144 A B a b f g) = (term1186 A B a b f g).
Proof. exact (MK_COMB (@lem5081026 A) (@lem5081025 A B a b f g)). Qed.
Lemma lem5081028 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1129 A B a b f g) = (term1186 A B a b f g).
Proof. exact (TRANS (@lem5080956 A B a b f g) (@lem5081027 A B a b f g)). Qed.
Lemma lem5081029 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1131 A B a b g) = (term1187 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081028 A B a b f g)). Qed.
Lemma lem5081030 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081031 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1132 A B a b g) = (term1188 A B a b g).
Proof. exact (MK_COMB (@lem5081030 A B) (@lem5081029 A B a b g)). Qed.
Lemma lem5081032 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1115 A B a b g) = (term1188 A B a b g).
Proof. exact (TRANS (@lem5080936 A B a b g) (@lem5081031 A B a b g)). Qed.
Lemma lem5081033 {A B : Type'} (a : A) (g : B -> A) : (term1117 A B a g) = (term1189 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081032 A B a b g)). Qed.
Lemma lem5081034 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081035 {A B : Type'} (a : A) (g : B -> A) : (term1118 A B a g) = (term1190 A B a g).
Proof. exact (MK_COMB (@lem5081034 B) (@lem5081033 A B a g)). Qed.
Lemma lem5081036 {A B : Type'} (a : A) (g : B -> A) : (term1106 A B a g) = (term1190 A B a g).
Proof. exact (TRANS (@lem5080916 A B a g) (@lem5081035 A B a g)). Qed.
Lemma lem5081037 {A B : Type'} (a : A) (g : B -> A) : (term836 A B a g) = (term1190 A B a g).
Proof. exact (TRANS (@lem5080896 A B a g) (@lem5081036 A B a g)). Qed.
Lemma lem5081038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081039 {A B : Type'} (a : A) (g : B -> A) : (term837 A B a g) = (term1191 A B a g).
Proof. exact (MK_COMB (@lem5081038) (@lem5081037 A B a g)). Qed.
Lemma lem5081041 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5081042 {B : Type'} (P : Prop) (Q : type686 B) : (term764 B P Q) = (term763 B P Q).
Proof. exact (@lem5081041 (B -> Prop) P Q). Qed.
Lemma lem5081043 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term839 A B b s a f g) = (term838 A B b s a f g).
Proof. exact (@lem5081042 B (@FINITE A s) (term840 A B b s a f g)). Qed.
Lemma lem5081044 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term841 A B b s a f g t) = (term720 A B t b s a f g).
Proof. exact (eq_refl (term841 A B b s a f g t)). Qed.
Lemma lem5081045 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term846 A B b s a f g) = (term840 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081044 A B t b s a f g)). Qed.
Lemma lem5081046 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081047 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term847 A B b s a f g) = (term848 A B b s a f g).
Proof. exact (MK_COMB (@lem5081046 B) (@lem5081045 A B b s a f g)). Qed.
Lemma lem5081048 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5081049 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term839 A B b s a f g) = (term849 A B b s a f g).
Proof. exact (MK_COMB (@lem5081048 A s) (@lem5081047 A B b s a f g)). Qed.
Lemma lem5081050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081051 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1192 A B b s a f g) = (term1193 A B b s a f g).
Proof. exact (MK_COMB (@lem5081050) (@lem5081049 A B b s a f g)). Qed.
Lemma lem5081052 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term841 A B b s a f g t) = (term720 A B t b s a f g).
Proof. exact (eq_refl (term841 A B b s a f g t)). Qed.
Lemma lem5081053 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5081054 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term842 A B b s a f g t) = (term723 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081053 A s) (@lem5081052 A B t b s a f g)). Qed.
Lemma lem5081055 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term843 A B b s a f g) = (term730 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081054 A B t b s a f g)). Qed.
Lemma lem5081056 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081057 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term838 A B b s a f g) = (term731 A B b s a f g).
Proof. exact (MK_COMB (@lem5081056 B) (@lem5081055 A B b s a f g)). Qed.
Lemma lem5081058 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : ((term839 A B b s a f g) = (term838 A B b s a f g)) = ((term849 A B b s a f g) = (term731 A B b s a f g)).
Proof. exact (MK_COMB (@lem5081051 A B b s a f g) (@lem5081057 A B b s a f g)). Qed.
Lemma lem5081059 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term849 A B b s a f g) = (term731 A B b s a f g).
Proof. exact (EQ_MP (@lem5081058 A B b s a f g) (@lem5081043 A B b s a f g)). Qed.
Lemma lem5081060 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term850 A B b a f g) = (term737 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081059 A B b s a f g)). Qed.
Lemma lem5081061 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081062 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term851 A B b a f g) = (term738 A B b a f g).
Proof. exact (MK_COMB (@lem5081061 A) (@lem5081060 A B b a f g)). Qed.
Lemma lem5081063 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term852 A B b a g) = (term744 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081062 A B b a f g)). Qed.
Lemma lem5081064 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081065 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term853 A B b a g) = (term745 A B b a g).
Proof. exact (MK_COMB (@lem5081064 A B) (@lem5081063 A B b a g)). Qed.
Lemma lem5081066 {A B : Type'} (a : A) (g : B -> A) : (term854 A B a g) = (term751 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081065 A B b a g)). Qed.
Lemma lem5081067 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081068 {A B : Type'} (a : A) (g : B -> A) : (term855 A B a g) = (term752 A B a g).
Proof. exact (MK_COMB (@lem5081067 B) (@lem5081066 A B a g)). Qed.
Lemma lem5081069 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081070 {A B : Type'} (a : A) (g : B -> A) : (term856 A B a g) = (term755 A B a g).
Proof. exact (MK_COMB (@lem5081069 A a) (@lem5081068 A B a g)). Qed.
Lemma lem5081072 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5081073 {B : Type'} (P : Prop) (Q : B -> Prop) : (term762 B P Q) = (term761 B P Q).
Proof. exact (@lem5081072 B P Q). Qed.
Lemma lem5081074 {A B : Type'} (a : A) (g : B -> A) : (term1194 A B a g) = (term1195 A B a g).
Proof. exact (@lem5081073 B (term705 A a) (term751 A B a g)). Qed.
Lemma lem5081075 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1196 A B a g b) = (term745 A B b a g).
Proof. exact (eq_refl (term1196 A B a g b)). Qed.
Lemma lem5081076 {A B : Type'} (a : A) (g : B -> A) : (term1197 A B a g) = (term751 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081075 A B b a g)). Qed.
Lemma lem5081077 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081078 {A B : Type'} (a : A) (g : B -> A) : (term1198 A B a g) = (term752 A B a g).
Proof. exact (MK_COMB (@lem5081077 B) (@lem5081076 A B a g)). Qed.
Lemma lem5081079 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081080 {A B : Type'} (a : A) (g : B -> A) : (term1194 A B a g) = (term755 A B a g).
Proof. exact (MK_COMB (@lem5081079 A a) (@lem5081078 A B a g)). Qed.
Lemma lem5081081 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081082 {A B : Type'} (a : A) (g : B -> A) : (term1199 A B a g) = (term1200 A B a g).
Proof. exact (MK_COMB (@lem5081081) (@lem5081080 A B a g)). Qed.
Lemma lem5081083 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1196 A B a g b) = (term745 A B b a g).
Proof. exact (eq_refl (term1196 A B a g b)). Qed.
Lemma lem5081084 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081085 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1201 A B a g b) = (term1202 A B b a g).
Proof. exact (MK_COMB (@lem5081084 A a) (@lem5081083 A B b a g)). Qed.
Lemma lem5081086 {A B : Type'} (a : A) (g : B -> A) : (term1203 A B a g) = (term1204 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081085 A B b a g)). Qed.
Lemma lem5081087 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081088 {A B : Type'} (a : A) (g : B -> A) : (term1195 A B a g) = (term1205 A B a g).
Proof. exact (MK_COMB (@lem5081087 B) (@lem5081086 A B a g)). Qed.
Lemma lem5081089 {A B : Type'} (a : A) (g : B -> A) : ((term1194 A B a g) = (term1195 A B a g)) = ((term755 A B a g) = (term1205 A B a g)).
Proof. exact (MK_COMB (@lem5081082 A B a g) (@lem5081088 A B a g)). Qed.
Lemma lem5081090 {A B : Type'} (a : A) (g : B -> A) : (term755 A B a g) = (term1205 A B a g).
Proof. exact (EQ_MP (@lem5081089 A B a g) (@lem5081074 A B a g)). Qed.
Lemma lem5081092 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5081093 {A B : Type'} (P : Prop) (Q : type572 A B) : (term1119 A B P Q) = (term1120 A B P Q).
Proof. exact (@lem5081092 (A -> B) P Q). Qed.
Lemma lem5081094 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1206 A B b a g) = (term1207 A B b a g).
Proof. exact (@lem5081093 A B (term705 A a) (term744 A B b a g)). Qed.
Lemma lem5081095 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1208 A B b a g f) = (term738 A B b a f g).
Proof. exact (eq_refl (term1208 A B b a g f)). Qed.
Lemma lem5081096 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1209 A B b a g) = (term744 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081095 A B b a f g)). Qed.
Lemma lem5081097 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081098 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1210 A B b a g) = (term745 A B b a g).
Proof. exact (MK_COMB (@lem5081097 A B) (@lem5081096 A B b a g)). Qed.
Lemma lem5081099 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081100 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1206 A B b a g) = (term1202 A B b a g).
Proof. exact (MK_COMB (@lem5081099 A a) (@lem5081098 A B b a g)). Qed.
Lemma lem5081101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081102 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1211 A B b a g) = (term1212 A B b a g).
Proof. exact (MK_COMB (@lem5081101) (@lem5081100 A B b a g)). Qed.
Lemma lem5081103 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1208 A B b a g f) = (term738 A B b a f g).
Proof. exact (eq_refl (term1208 A B b a g f)). Qed.
Lemma lem5081104 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081105 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1213 A B b a g f) = (term1214 A B b a f g).
Proof. exact (MK_COMB (@lem5081104 A a) (@lem5081103 A B b a f g)). Qed.
Lemma lem5081106 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1215 A B b a g) = (term1216 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081105 A B b a f g)). Qed.
Lemma lem5081107 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081108 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1207 A B b a g) = (term1217 A B b a g).
Proof. exact (MK_COMB (@lem5081107 A B) (@lem5081106 A B b a g)). Qed.
Lemma lem5081109 {A B : Type'} (b : B) (a : A) (g : B -> A) : ((term1206 A B b a g) = (term1207 A B b a g)) = ((term1202 A B b a g) = (term1217 A B b a g)).
Proof. exact (MK_COMB (@lem5081102 A B b a g) (@lem5081108 A B b a g)). Qed.
Lemma lem5081110 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1202 A B b a g) = (term1217 A B b a g).
Proof. exact (EQ_MP (@lem5081109 A B b a g) (@lem5081094 A B b a g)). Qed.
Lemma lem5081112 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5081113 {A : Type'} (P : Prop) (Q : type686 A) : (term764 A P Q) = (term763 A P Q).
Proof. exact (@lem5081112 (A -> Prop) P Q). Qed.
Lemma lem5081114 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1218 A B b a f g) = (term1219 A B b a f g).
Proof. exact (@lem5081113 A (term705 A a) (term737 A B b a f g)). Qed.
Lemma lem5081115 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1220 A B b a f g s) = (term731 A B b s a f g).
Proof. exact (eq_refl (term1220 A B b a f g s)). Qed.
Lemma lem5081116 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1221 A B b a f g) = (term737 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081115 A B b s a f g)). Qed.
Lemma lem5081117 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081118 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1222 A B b a f g) = (term738 A B b a f g).
Proof. exact (MK_COMB (@lem5081117 A) (@lem5081116 A B b a f g)). Qed.
Lemma lem5081119 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081120 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1218 A B b a f g) = (term1214 A B b a f g).
Proof. exact (MK_COMB (@lem5081119 A a) (@lem5081118 A B b a f g)). Qed.
Lemma lem5081121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081122 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1223 A B b a f g) = (term1224 A B b a f g).
Proof. exact (MK_COMB (@lem5081121) (@lem5081120 A B b a f g)). Qed.
Lemma lem5081123 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1220 A B b a f g s) = (term731 A B b s a f g).
Proof. exact (eq_refl (term1220 A B b a f g s)). Qed.
Lemma lem5081124 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081125 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1225 A B b a f g s) = (term1226 A B b s a f g).
Proof. exact (MK_COMB (@lem5081124 A a) (@lem5081123 A B b s a f g)). Qed.
Lemma lem5081126 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1227 A B b a f g) = (term1228 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081125 A B b s a f g)). Qed.
Lemma lem5081127 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081128 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1219 A B b a f g) = (term1229 A B b a f g).
Proof. exact (MK_COMB (@lem5081127 A) (@lem5081126 A B b a f g)). Qed.
Lemma lem5081129 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : ((term1218 A B b a f g) = (term1219 A B b a f g)) = ((term1214 A B b a f g) = (term1229 A B b a f g)).
Proof. exact (MK_COMB (@lem5081122 A B b a f g) (@lem5081128 A B b a f g)). Qed.
Lemma lem5081130 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1214 A B b a f g) = (term1229 A B b a f g).
Proof. exact (EQ_MP (@lem5081129 A B b a f g) (@lem5081114 A B b a f g)). Qed.
Lemma lem5081132 {A : Type'} (P : Prop) (Q : A -> Prop) : (term762 A P Q) = (term761 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5081133 {B : Type'} (P : Prop) (Q : type686 B) : (term764 B P Q) = (term763 B P Q).
Proof. exact (@lem5081132 (B -> Prop) P Q). Qed.
Lemma lem5081134 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1230 A B b s a f g) = (term1231 A B b s a f g).
Proof. exact (@lem5081133 B (term705 A a) (term730 A B b s a f g)). Qed.
Lemma lem5081135 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1232 A B b s a f g t) = (term723 A B t b s a f g).
Proof. exact (eq_refl (term1232 A B b s a f g t)). Qed.
Lemma lem5081136 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1233 A B b s a f g) = (term730 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081135 A B t b s a f g)). Qed.
Lemma lem5081137 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081138 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1234 A B b s a f g) = (term731 A B b s a f g).
Proof. exact (MK_COMB (@lem5081137 B) (@lem5081136 A B b s a f g)). Qed.
Lemma lem5081139 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081140 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1230 A B b s a f g) = (term1226 A B b s a f g).
Proof. exact (MK_COMB (@lem5081139 A a) (@lem5081138 A B b s a f g)). Qed.
Lemma lem5081141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081142 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1235 A B b s a f g) = (term1236 A B b s a f g).
Proof. exact (MK_COMB (@lem5081141) (@lem5081140 A B b s a f g)). Qed.
Lemma lem5081143 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1232 A B b s a f g t) = (term723 A B t b s a f g).
Proof. exact (eq_refl (term1232 A B b s a f g t)). Qed.
Lemma lem5081144 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081145 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1237 A B b s a f g t) = (term1238 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081144 A a) (@lem5081143 A B t b s a f g)). Qed.
Lemma lem5081146 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1239 A B b s a f g) = (term1240 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081145 A B t b s a f g)). Qed.
Lemma lem5081147 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081148 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1231 A B b s a f g) = (term1241 A B b s a f g).
Proof. exact (MK_COMB (@lem5081147 B) (@lem5081146 A B b s a f g)). Qed.
Lemma lem5081149 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : ((term1230 A B b s a f g) = (term1231 A B b s a f g)) = ((term1226 A B b s a f g) = (term1241 A B b s a f g)).
Proof. exact (MK_COMB (@lem5081142 A B b s a f g) (@lem5081148 A B b s a f g)). Qed.
Lemma lem5081150 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1226 A B b s a f g) = (term1241 A B b s a f g).
Proof. exact (EQ_MP (@lem5081149 A B b s a f g) (@lem5081134 A B b s a f g)). Qed.
Lemma lem5081151 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1228 A B b a f g) = (term1242 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081150 A B b s a f g)). Qed.
Lemma lem5081152 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081153 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1229 A B b a f g) = (term1243 A B b a f g).
Proof. exact (MK_COMB (@lem5081152 A) (@lem5081151 A B b a f g)). Qed.
Lemma lem5081154 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1214 A B b a f g) = (term1243 A B b a f g).
Proof. exact (TRANS (@lem5081130 A B b a f g) (@lem5081153 A B b a f g)). Qed.
Lemma lem5081155 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1216 A B b a g) = (term1244 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081154 A B b a f g)). Qed.
Lemma lem5081156 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081157 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1217 A B b a g) = (term1245 A B b a g).
Proof. exact (MK_COMB (@lem5081156 A B) (@lem5081155 A B b a g)). Qed.
Lemma lem5081158 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1202 A B b a g) = (term1245 A B b a g).
Proof. exact (TRANS (@lem5081110 A B b a g) (@lem5081157 A B b a g)). Qed.
Lemma lem5081159 {A B : Type'} (a : A) (g : B -> A) : (term1204 A B a g) = (term1246 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081158 A B b a g)). Qed.
Lemma lem5081160 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081161 {A B : Type'} (a : A) (g : B -> A) : (term1205 A B a g) = (term1247 A B a g).
Proof. exact (MK_COMB (@lem5081160 B) (@lem5081159 A B a g)). Qed.
Lemma lem5081162 {A B : Type'} (a : A) (g : B -> A) : (term755 A B a g) = (term1247 A B a g).
Proof. exact (TRANS (@lem5081090 A B a g) (@lem5081161 A B a g)). Qed.
Lemma lem5081163 {A B : Type'} (a : A) (g : B -> A) : (term856 A B a g) = (term1247 A B a g).
Proof. exact (TRANS (@lem5081070 A B a g) (@lem5081162 A B a g)). Qed.
Lemma lem5081164 {A B : Type'} (a : A) (g : B -> A) : (term857 A B a g) = (term1248 A B a g).
Proof. exact (MK_COMB (@lem5081039 A B a g) (@lem5081163 A B a g)). Qed.
Lemma lem5081166 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term778 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5081167 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term778 B P Q) = (term777 B P Q).
Proof. exact (@lem5081166 B P Q). Qed.
Lemma lem5081168 {A B : Type'} (a : A) (g : B -> A) : (term1249 A B a g) = (term1250 A B a g).
Proof. exact (@lem5081167 B (term1189 A B a g) (term1246 A B a g)). Qed.
Lemma lem5081169 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1251 A B a g b) = (term1188 A B a b g).
Proof. exact (eq_refl (term1251 A B a g b)). Qed.
Lemma lem5081170 {A B : Type'} (a : A) (g : B -> A) : (term1252 A B a g) = (term1189 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081169 A B a b g)). Qed.
Lemma lem5081171 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081172 {A B : Type'} (a : A) (g : B -> A) : (term1253 A B a g) = (term1190 A B a g).
Proof. exact (MK_COMB (@lem5081171 B) (@lem5081170 A B a g)). Qed.
Lemma lem5081173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081174 {A B : Type'} (a : A) (g : B -> A) : (term1254 A B a g) = (term1191 A B a g).
Proof. exact (MK_COMB (@lem5081173) (@lem5081172 A B a g)). Qed.
Lemma lem5081175 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1255 A B a g b) = (term1245 A B b a g).
Proof. exact (eq_refl (term1255 A B a g b)). Qed.
Lemma lem5081176 {A B : Type'} (a : A) (g : B -> A) : (term1256 A B a g) = (term1246 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081175 A B b a g)). Qed.
Lemma lem5081177 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081178 {A B : Type'} (a : A) (g : B -> A) : (term1257 A B a g) = (term1247 A B a g).
Proof. exact (MK_COMB (@lem5081177 B) (@lem5081176 A B a g)). Qed.
Lemma lem5081179 {A B : Type'} (a : A) (g : B -> A) : (term1249 A B a g) = (term1248 A B a g).
Proof. exact (MK_COMB (@lem5081174 A B a g) (@lem5081178 A B a g)). Qed.
Lemma lem5081180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081181 {A B : Type'} (a : A) (g : B -> A) : (term1258 A B a g) = (term1259 A B a g).
Proof. exact (MK_COMB (@lem5081180) (@lem5081179 A B a g)). Qed.
Lemma lem5081182 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1251 A B a g b) = (term1188 A B a b g).
Proof. exact (eq_refl (term1251 A B a g b)). Qed.
Lemma lem5081183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081184 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1260 A B a g b) = (term1261 A B a b g).
Proof. exact (MK_COMB (@lem5081183) (@lem5081182 A B a b g)). Qed.
Lemma lem5081185 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1255 A B a g b) = (term1245 A B b a g).
Proof. exact (eq_refl (term1255 A B a g b)). Qed.
Lemma lem5081186 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1262 A B a g b) = (term1263 A B b a g).
Proof. exact (MK_COMB (@lem5081184 A B a b g) (@lem5081185 A B b a g)). Qed.
Lemma lem5081187 {A B : Type'} (a : A) (g : B -> A) : (term1264 A B a g) = (term1265 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081186 A B b a g)). Qed.
Lemma lem5081188 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081189 {A B : Type'} (a : A) (g : B -> A) : (term1250 A B a g) = (term1266 A B a g).
Proof. exact (MK_COMB (@lem5081188 B) (@lem5081187 A B a g)). Qed.
Lemma lem5081190 {A B : Type'} (a : A) (g : B -> A) : ((term1249 A B a g) = (term1250 A B a g)) = ((term1248 A B a g) = (term1266 A B a g)).
Proof. exact (MK_COMB (@lem5081181 A B a g) (@lem5081189 A B a g)). Qed.
Lemma lem5081191 {A B : Type'} (a : A) (g : B -> A) : (term1248 A B a g) = (term1266 A B a g).
Proof. exact (EQ_MP (@lem5081190 A B a g) (@lem5081168 A B a g)). Qed.
Lemma lem5081193 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term778 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5081194 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term1267 A B P Q) = (term1268 A B P Q).
Proof. exact (@lem5081193 (A -> B) P Q). Qed.
Lemma lem5081195 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1269 A B b a g) = (term1270 A B b a g).
Proof. exact (@lem5081194 A B (term1187 A B a b g) (term1244 A B b a g)). Qed.
Lemma lem5081196 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1271 A B a b g f) = (term1186 A B a b f g).
Proof. exact (eq_refl (term1271 A B a b g f)). Qed.
Lemma lem5081197 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1272 A B a b g) = (term1187 A B a b g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081196 A B a b f g)). Qed.
Lemma lem5081198 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081199 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1273 A B a b g) = (term1188 A B a b g).
Proof. exact (MK_COMB (@lem5081198 A B) (@lem5081197 A B a b g)). Qed.
Lemma lem5081200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081201 {A B : Type'} (a : A) (b : B) (g : B -> A) : (term1274 A B a b g) = (term1261 A B a b g).
Proof. exact (MK_COMB (@lem5081200) (@lem5081199 A B a b g)). Qed.
Lemma lem5081202 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1275 A B b a g f) = (term1243 A B b a f g).
Proof. exact (eq_refl (term1275 A B b a g f)). Qed.
Lemma lem5081203 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1276 A B b a g) = (term1244 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081202 A B b a f g)). Qed.
Lemma lem5081204 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081205 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1277 A B b a g) = (term1245 A B b a g).
Proof. exact (MK_COMB (@lem5081204 A B) (@lem5081203 A B b a g)). Qed.
Lemma lem5081206 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1269 A B b a g) = (term1263 A B b a g).
Proof. exact (MK_COMB (@lem5081201 A B a b g) (@lem5081205 A B b a g)). Qed.
Lemma lem5081207 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081208 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1278 A B b a g) = (term1279 A B b a g).
Proof. exact (MK_COMB (@lem5081207) (@lem5081206 A B b a g)). Qed.
Lemma lem5081209 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1271 A B a b g f) = (term1186 A B a b f g).
Proof. exact (eq_refl (term1271 A B a b g f)). Qed.
Lemma lem5081210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081211 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1280 A B a b g f) = (term1281 A B a b f g).
Proof. exact (MK_COMB (@lem5081210) (@lem5081209 A B a b f g)). Qed.
Lemma lem5081212 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1275 A B b a g f) = (term1243 A B b a f g).
Proof. exact (eq_refl (term1275 A B b a g f)). Qed.
Lemma lem5081213 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1282 A B b a g f) = (term1283 A B b a f g).
Proof. exact (MK_COMB (@lem5081211 A B a b f g) (@lem5081212 A B b a f g)). Qed.
Lemma lem5081214 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1284 A B b a g) = (term1285 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081213 A B b a f g)). Qed.
Lemma lem5081215 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081216 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1270 A B b a g) = (term1286 A B b a g).
Proof. exact (MK_COMB (@lem5081215 A B) (@lem5081214 A B b a g)). Qed.
Lemma lem5081217 {A B : Type'} (b : B) (a : A) (g : B -> A) : ((term1269 A B b a g) = (term1270 A B b a g)) = ((term1263 A B b a g) = (term1286 A B b a g)).
Proof. exact (MK_COMB (@lem5081208 A B b a g) (@lem5081216 A B b a g)). Qed.
Lemma lem5081218 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1263 A B b a g) = (term1286 A B b a g).
Proof. exact (EQ_MP (@lem5081217 A B b a g) (@lem5081195 A B b a g)). Qed.
Lemma lem5081220 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term778 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5081221 {A : Type'} (P : type686 A) (Q : type686 A) : (term1287 A P Q) = (term1288 A P Q).
Proof. exact (@lem5081220 (A -> Prop) P Q). Qed.
Lemma lem5081222 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1289 A B b a f g) = (term1290 A B b a f g).
Proof. exact (@lem5081221 A (term1185 A B a b f g) (term1242 A B b a f g)). Qed.
Lemma lem5081223 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1291 A B a b f g s) = (term1184 A B a b s f g).
Proof. exact (eq_refl (term1291 A B a b f g s)). Qed.
Lemma lem5081224 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1292 A B a b f g) = (term1185 A B a b f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081223 A B a b s f g)). Qed.
Lemma lem5081225 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081226 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1293 A B a b f g) = (term1186 A B a b f g).
Proof. exact (MK_COMB (@lem5081225 A) (@lem5081224 A B a b f g)). Qed.
Lemma lem5081227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081228 {A B : Type'} (a : A) (b : B) (f : A -> B) (g : B -> A) : (term1294 A B a b f g) = (term1281 A B a b f g).
Proof. exact (MK_COMB (@lem5081227) (@lem5081226 A B a b f g)). Qed.
Lemma lem5081229 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1295 A B b a f g s) = (term1241 A B b s a f g).
Proof. exact (eq_refl (term1295 A B b a f g s)). Qed.
Lemma lem5081230 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1296 A B b a f g) = (term1242 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081229 A B b s a f g)). Qed.
Lemma lem5081231 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081232 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1297 A B b a f g) = (term1243 A B b a f g).
Proof. exact (MK_COMB (@lem5081231 A) (@lem5081230 A B b a f g)). Qed.
Lemma lem5081233 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1289 A B b a f g) = (term1283 A B b a f g).
Proof. exact (MK_COMB (@lem5081228 A B a b f g) (@lem5081232 A B b a f g)). Qed.
Lemma lem5081234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081235 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1298 A B b a f g) = (term1299 A B b a f g).
Proof. exact (MK_COMB (@lem5081234) (@lem5081233 A B b a f g)). Qed.
Lemma lem5081236 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1291 A B a b f g s) = (term1184 A B a b s f g).
Proof. exact (eq_refl (term1291 A B a b f g s)). Qed.
Lemma lem5081237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081238 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1300 A B a b f g s) = (term1301 A B a b s f g).
Proof. exact (MK_COMB (@lem5081237) (@lem5081236 A B a b s f g)). Qed.
Lemma lem5081239 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1295 A B b a f g s) = (term1241 A B b s a f g).
Proof. exact (eq_refl (term1295 A B b a f g s)). Qed.
Lemma lem5081240 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1302 A B b a f g s) = (term1303 A B b s a f g).
Proof. exact (MK_COMB (@lem5081238 A B a b s f g) (@lem5081239 A B b s a f g)). Qed.
Lemma lem5081241 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1304 A B b a f g) = (term1305 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081240 A B b s a f g)). Qed.
Lemma lem5081242 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081243 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1290 A B b a f g) = (term1306 A B b a f g).
Proof. exact (MK_COMB (@lem5081242 A) (@lem5081241 A B b a f g)). Qed.
Lemma lem5081244 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : ((term1289 A B b a f g) = (term1290 A B b a f g)) = ((term1283 A B b a f g) = (term1306 A B b a f g)).
Proof. exact (MK_COMB (@lem5081235 A B b a f g) (@lem5081243 A B b a f g)). Qed.
Lemma lem5081245 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1283 A B b a f g) = (term1306 A B b a f g).
Proof. exact (EQ_MP (@lem5081244 A B b a f g) (@lem5081222 A B b a f g)). Qed.
Lemma lem5081247 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term778 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5081248 {B : Type'} (P : type686 B) (Q : type686 B) : (term1287 B P Q) = (term1288 B P Q).
Proof. exact (@lem5081247 (B -> Prop) P Q). Qed.
Lemma lem5081249 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1307 A B b s a f g) = (term1308 A B b s a f g).
Proof. exact (@lem5081248 B (term1183 A B a b s f g) (term1240 A B b s a f g)). Qed.
Lemma lem5081250 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1309 A B a b s f g t) = (term1182 A B a b t s f g).
Proof. exact (eq_refl (term1309 A B a b s f g t)). Qed.
Lemma lem5081251 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1310 A B a b s f g) = (term1183 A B a b s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081250 A B a b t s f g)). Qed.
Lemma lem5081252 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081253 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1311 A B a b s f g) = (term1184 A B a b s f g).
Proof. exact (MK_COMB (@lem5081252 B) (@lem5081251 A B a b s f g)). Qed.
Lemma lem5081254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081255 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1312 A B a b s f g) = (term1301 A B a b s f g).
Proof. exact (MK_COMB (@lem5081254) (@lem5081253 A B a b s f g)). Qed.
Lemma lem5081256 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1313 A B b s a f g t) = (term1238 A B t b s a f g).
Proof. exact (eq_refl (term1313 A B b s a f g t)). Qed.
Lemma lem5081257 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1314 A B b s a f g) = (term1240 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081256 A B t b s a f g)). Qed.
Lemma lem5081258 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081259 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1315 A B b s a f g) = (term1241 A B b s a f g).
Proof. exact (MK_COMB (@lem5081258 B) (@lem5081257 A B b s a f g)). Qed.
Lemma lem5081260 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1307 A B b s a f g) = (term1303 A B b s a f g).
Proof. exact (MK_COMB (@lem5081255 A B a b s f g) (@lem5081259 A B b s a f g)). Qed.
Lemma lem5081261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081262 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1316 A B b s a f g) = (term1317 A B b s a f g).
Proof. exact (MK_COMB (@lem5081261) (@lem5081260 A B b s a f g)). Qed.
Lemma lem5081263 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1309 A B a b s f g t) = (term1182 A B a b t s f g).
Proof. exact (eq_refl (term1309 A B a b s f g t)). Qed.
Lemma lem5081264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081265 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1318 A B a b s f g t) = (term1319 A B a b t s f g).
Proof. exact (MK_COMB (@lem5081264) (@lem5081263 A B a b t s f g)). Qed.
Lemma lem5081266 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1313 A B b s a f g t) = (term1238 A B t b s a f g).
Proof. exact (eq_refl (term1313 A B b s a f g t)). Qed.
Lemma lem5081267 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1320 A B b s a f g t) = (term1321 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081265 A B a b t s f g) (@lem5081266 A B t b s a f g)). Qed.
Lemma lem5081268 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1322 A B b s a f g) = (term1323 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081267 A B t b s a f g)). Qed.
Lemma lem5081269 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081270 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1308 A B b s a f g) = (term1324 A B b s a f g).
Proof. exact (MK_COMB (@lem5081269 B) (@lem5081268 A B b s a f g)). Qed.
Lemma lem5081271 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : ((term1307 A B b s a f g) = (term1308 A B b s a f g)) = ((term1303 A B b s a f g) = (term1324 A B b s a f g)).
Proof. exact (MK_COMB (@lem5081262 A B b s a f g) (@lem5081270 A B b s a f g)). Qed.
Lemma lem5081272 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1303 A B b s a f g) = (term1324 A B b s a f g).
Proof. exact (EQ_MP (@lem5081271 A B b s a f g) (@lem5081249 A B b s a f g)). Qed.
Lemma lem5081274 {A : Type'} (P : A -> Prop) (Q : Prop) : (term862 A P Q) = (term863 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5081275 {A : Type'} (P : A -> Prop) (Q : Prop) : (term862 A P Q) = (term863 A P Q).
Proof. exact (@lem5081274 A P Q). Qed.
Lemma lem5081276 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1325 A B t b s a f g) = (term1326 A B t b s a f g).
Proof. exact (@lem5081275 A (term1181 A B a b t s f g) (term1238 A B t b s a f g)). Qed.
Lemma lem5081277 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1327 A B a b t s f g x) = (term1180 A B x a b t s f g).
Proof. exact (eq_refl (term1327 A B a b t s f g x)). Qed.
Lemma lem5081278 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1328 A B a b t s f g) = (term1181 A B a b t s f g).
Proof. exact (fun_ext (fun x : A => @lem5081277 A B x a b t s f g)). Qed.
Lemma lem5081279 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5081280 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1329 A B a b t s f g) = (term1182 A B a b t s f g).
Proof. exact (MK_COMB (@lem5081279 A) (@lem5081278 A B a b t s f g)). Qed.
Lemma lem5081281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081282 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1330 A B a b t s f g) = (term1319 A B a b t s f g).
Proof. exact (MK_COMB (@lem5081281) (@lem5081280 A B a b t s f g)). Qed.
Lemma lem5081283 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1238 A B t b s a f g) = (term1238 A B t b s a f g).
Proof. exact (eq_refl (term1238 A B t b s a f g)). Qed.
Lemma lem5081284 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1325 A B t b s a f g) = (term1321 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081282 A B a b t s f g) (@lem5081283 A B t b s a f g)). Qed.
Lemma lem5081285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081286 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1331 A B t b s a f g) = (term1332 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081285) (@lem5081284 A B t b s a f g)). Qed.
Lemma lem5081287 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1327 A B a b t s f g x) = (term1180 A B x a b t s f g).
Proof. exact (eq_refl (term1327 A B a b t s f g x)). Qed.
Lemma lem5081288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081289 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1333 A B a b t s f g x) = (term1334 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5081288) (@lem5081287 A B x a b t s f g)). Qed.
Lemma lem5081290 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1238 A B t b s a f g) = (term1238 A B t b s a f g).
Proof. exact (eq_refl (term1238 A B t b s a f g)). Qed.
Lemma lem5081291 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1335 A B x t b s a f g) = (term1336 A B x t b s a f g).
Proof. exact (MK_COMB (@lem5081289 A B x a b t s f g) (@lem5081290 A B t b s a f g)). Qed.
Lemma lem5081292 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1337 A B t b s a f g) = (term1338 A B t b s a f g).
Proof. exact (fun_ext (fun x : A => @lem5081291 A B x t b s a f g)). Qed.
Lemma lem5081293 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5081294 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1326 A B t b s a f g) = (term1339 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081293 A) (@lem5081292 A B t b s a f g)). Qed.
Lemma lem5081295 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : ((term1325 A B t b s a f g) = (term1326 A B t b s a f g)) = ((term1321 A B t b s a f g) = (term1339 A B t b s a f g)).
Proof. exact (MK_COMB (@lem5081286 A B t b s a f g) (@lem5081294 A B t b s a f g)). Qed.
Lemma lem5081296 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1321 A B t b s a f g) = (term1339 A B t b s a f g).
Proof. exact (EQ_MP (@lem5081295 A B t b s a f g) (@lem5081276 A B t b s a f g)). Qed.
Lemma lem5081298 {A : Type'} (P : A -> Prop) (Q : Prop) : (term862 A P Q) = (term863 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5081299 {B : Type'} (P : B -> Prop) (Q : Prop) : (term862 B P Q) = (term863 B P Q).
Proof. exact (@lem5081298 B P Q). Qed.
Lemma lem5081300 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1340 A B x t b s a f g) = (term1341 A B x t b s a f g).
Proof. exact (@lem5081299 B (term1179 A B x a b t s f g) (term1238 A B t b s a f g)). Qed.
Lemma lem5081301 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1342 A B x a b t s f g y) = (term1177 A B x a b t s f g y).
Proof. exact (eq_refl (term1342 A B x a b t s f g y)). Qed.
Lemma lem5081302 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1343 A B x a b t s f g) = (term1179 A B x a b t s f g).
Proof. exact (fun_ext (fun y : B => @lem5081301 A B x a b t s f g y)). Qed.
Lemma lem5081303 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081304 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1344 A B x a b t s f g) = (term1180 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5081303 B) (@lem5081302 A B x a b t s f g)). Qed.
Lemma lem5081305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081306 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term1345 A B x a b t s f g) = (term1334 A B x a b t s f g).
Proof. exact (MK_COMB (@lem5081305) (@lem5081304 A B x a b t s f g)). Qed.
Lemma lem5081307 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1238 A B t b s a f g) = (term1238 A B t b s a f g).
Proof. exact (eq_refl (term1238 A B t b s a f g)). Qed.
Lemma lem5081308 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1340 A B x t b s a f g) = (term1336 A B x t b s a f g).
Proof. exact (MK_COMB (@lem5081306 A B x a b t s f g) (@lem5081307 A B t b s a f g)). Qed.
Lemma lem5081309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5081310 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1346 A B x t b s a f g) = (term1347 A B x t b s a f g).
Proof. exact (MK_COMB (@lem5081309) (@lem5081308 A B x t b s a f g)). Qed.
Lemma lem5081311 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1342 A B x a b t s f g y) = (term1177 A B x a b t s f g y).
Proof. exact (eq_refl (term1342 A B x a b t s f g y)). Qed.
Lemma lem5081312 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5081313 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1348 A B x a b t s f g y) = (term1349 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5081312) (@lem5081311 A B x a b t s f g y)). Qed.
Lemma lem5081314 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1238 A B t b s a f g) = (term1238 A B t b s a f g).
Proof. exact (eq_refl (term1238 A B t b s a f g)). Qed.
Lemma lem5081315 {A B : Type'} (x : A) (y : B) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1350 A B x y t b s a f g) = (term1351 A B x y t b s a f g).
Proof. exact (MK_COMB (@lem5081313 A B x a b t s f g y) (@lem5081314 A B t b s a f g)). Qed.
Lemma lem5081316 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1352 A B x t b s a f g) = (term1353 A B x t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5081315 A B x y t b s a f g)). Qed.
Lemma lem5081317 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081318 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1341 A B x t b s a f g) = (term1354 A B x t b s a f g).
Proof. exact (MK_COMB (@lem5081317 B) (@lem5081316 A B x t b s a f g)). Qed.
Lemma lem5081319 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : ((term1340 A B x t b s a f g) = (term1341 A B x t b s a f g)) = ((term1336 A B x t b s a f g) = (term1354 A B x t b s a f g)).
Proof. exact (MK_COMB (@lem5081310 A B x t b s a f g) (@lem5081318 A B x t b s a f g)). Qed.
Lemma lem5081320 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1336 A B x t b s a f g) = (term1354 A B x t b s a f g).
Proof. exact (EQ_MP (@lem5081319 A B x t b s a f g) (@lem5081300 A B x t b s a f g)). Qed.
Lemma lem5081321 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1338 A B t b s a f g) = (term1355 A B t b s a f g).
Proof. exact (fun_ext (fun x : A => @lem5081320 A B x t b s a f g)). Qed.
Lemma lem5081322 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5081323 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1339 A B t b s a f g) = (term1356 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081322 A) (@lem5081321 A B t b s a f g)). Qed.
Lemma lem5081324 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1321 A B t b s a f g) = (term1356 A B t b s a f g).
Proof. exact (TRANS (@lem5081296 A B t b s a f g) (@lem5081323 A B t b s a f g)). Qed.
Lemma lem5081325 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1323 A B b s a f g) = (term1357 A B b s a f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5081324 A B t b s a f g)). Qed.
Lemma lem5081326 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem5081327 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1324 A B b s a f g) = (term1358 A B b s a f g).
Proof. exact (MK_COMB (@lem5081326 B) (@lem5081325 A B b s a f g)). Qed.
Lemma lem5081328 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1303 A B b s a f g) = (term1358 A B b s a f g).
Proof. exact (TRANS (@lem5081272 A B b s a f g) (@lem5081327 A B b s a f g)). Qed.
Lemma lem5081329 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1305 A B b a f g) = (term1359 A B b a f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5081328 A B b s a f g)). Qed.
Lemma lem5081330 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5081331 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1306 A B b a f g) = (term1360 A B b a f g).
Proof. exact (MK_COMB (@lem5081330 A) (@lem5081329 A B b a f g)). Qed.
Lemma lem5081332 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) : (term1283 A B b a f g) = (term1360 A B b a f g).
Proof. exact (TRANS (@lem5081245 A B b a f g) (@lem5081331 A B b a f g)). Qed.
Lemma lem5081333 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1285 A B b a g) = (term1361 A B b a g).
Proof. exact (fun_ext (fun f : A -> B => @lem5081332 A B b a f g)). Qed.
Lemma lem5081334 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem5081335 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1286 A B b a g) = (term1362 A B b a g).
Proof. exact (MK_COMB (@lem5081334 A B) (@lem5081333 A B b a g)). Qed.
Lemma lem5081336 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1263 A B b a g) = (term1362 A B b a g).
Proof. exact (TRANS (@lem5081218 A B b a g) (@lem5081335 A B b a g)). Qed.
Lemma lem5081337 {A B : Type'} (a : A) (g : B -> A) : (term1265 A B a g) = (term1363 A B a g).
Proof. exact (fun_ext (fun b : B => @lem5081336 A B b a g)). Qed.
Lemma lem5081338 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5081339 {A B : Type'} (a : A) (g : B -> A) : (term1266 A B a g) = (term1364 A B a g).
Proof. exact (MK_COMB (@lem5081338 B) (@lem5081337 A B a g)). Qed.
Lemma lem5081340 {A B : Type'} (a : A) (g : B -> A) : (term1248 A B a g) = (term1364 A B a g).
Proof. exact (TRANS (@lem5081191 A B a g) (@lem5081339 A B a g)). Qed.
Lemma lem5081341 {A B : Type'} (a : A) (g : B -> A) : (term857 A B a g) = (term1364 A B a g).
Proof. exact (TRANS (@lem5081164 A B a g) (@lem5081340 A B a g)). Qed.
Lemma lem5081342 {A B : Type'} (a : A) (g : B -> A) : (term760 A B a g) = (term1364 A B a g).
Proof. exact (TRANS (@lem5080421 A B a g) (@lem5081341 A B a g)). Qed.
Lemma lem5081343 {A B : Type'} (a : A) (g : B -> A) : (term499 A B a g) = (term1364 A B a g).
Proof. exact (TRANS (@lem5079717 A B a g) (@lem5081342 A B a g)). Qed.
Lemma lem5081344 {A B : Type'} (a : A) (g : B -> A) (h1 : term499 A B a g) : term1364 A B a g.
Proof. exact (EQ_MP (@lem5081343 A B a g) (@lem5079194 A B a g h1)). Qed.
Lemma lem5081345 {A B : Type'} (b : B) (a : A) (g : B -> A) (h1 : term1362 A B b a g) : term1362 A B b a g.
Proof. exact (h1). Qed.
Lemma lem5081346 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) (h1 : term1360 A B b a f g) : term1360 A B b a f g.
Proof. exact (h1). Qed.
Lemma lem5081347 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1358 A B b s a f g) : term1358 A B b s a f g.
Proof. exact (h1). Qed.
Lemma lem5081348 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1356 A B t b s a f g) : term1356 A B t b s a f g.
Proof. exact (h1). Qed.
Lemma lem5081349 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1354 A B x t b s a f g) : term1354 A B x t b s a f g.
Proof. exact (h1). Qed.
Lemma lem5081350 {A B : Type'} (x : A) (y : B) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1351 A B x y t b s a f g) : term1351 A B x y t b s a f g.
Proof. exact (h1). Qed.
Lemma lem5081399 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term514 A B t b s a f g y).
Proof. exact (eq_refl (term514 A B t b s a f g y)). Qed.
Lemma lem5081400 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term515 A B t b s a f g) = (term515 A B t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5081399 A B t b s a f g y)). Qed.
Lemma lem5081401 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5081402 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term516 A B t b s a f g) = (term516 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081401 B) (@lem5081400 A B t b s a f g)). Qed.
Lemma lem5081451 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term510 A B s a t b g f x).
Proof. exact (eq_refl (term510 A B s a t b g f x)). Qed.
Lemma lem5081452 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term511 A B s a t b g f) = (term511 A B s a t b g f).
Proof. exact (fun_ext (fun x : A => @lem5081451 A B s a t b g f x)). Qed.
Lemma lem5081453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5081454 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term512 A B s a t b g f) = (term512 A B s a t b g f).
Proof. exact (MK_COMB (@lem5081453 A) (@lem5081452 A B s a t b g f)). Qed.
Lemma lem5081455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5081456 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (MK_COMB (@lem5081455) (@lem5081454 A B s a t b g f)). Qed.
Lemma lem5081457 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term708 A B t b s a f g) = (term708 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081456 A B s a t b g f) (@lem5081402 A B t b s a f g)). Qed.
Lemma lem5081464 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5081465 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term711 A B t b s a f g) = (term711 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081464 B b t) (@lem5081457 A B t b s a f g)). Qed.
Lemma lem5081472 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5081473 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term714 A B t b s a f g) = (term714 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081472 A a s) (@lem5081465 A B t b s a f g)). Qed.
Lemma lem5081484 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5081485 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term717 A B t b s a f g) = (term717 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081484 A B s t) (@lem5081473 A B t b s a f g)). Qed.
Lemma lem5081490 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5081491 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term720 A B t b s a f g) = (term720 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081490 B t) (@lem5081485 A B t b s a f g)). Qed.
Lemma lem5081496 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5081497 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term723 A B t b s a f g) = (term723 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081496 A s) (@lem5081491 A B t b s a f g)). Qed.
Lemma lem5081506 {A : Type'} (a : A) : (term753 A a) = (term753 A a).
Proof. exact (eq_refl (term753 A a)). Qed.
Lemma lem5081507 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1238 A B t b s a f g) = (term1238 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081506 A a) (@lem5081497 A B t b s a f g)). Qed.
Lemma lem5081860 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term889 A B x a b t s f g y) = (term889 A B x a b t s f g y).
Proof. exact (eq_refl (term889 A B x a b t s f g y)). Qed.
Lemma lem5081909 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term514 A B t b s a f g y).
Proof. exact (eq_refl (term514 A B t b s a f g y)). Qed.
Lemma lem5081910 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term515 A B t b s a f g) = (term515 A B t b s a f g).
Proof. exact (fun_ext (fun y : B => @lem5081909 A B t b s a f g y)). Qed.
Lemma lem5081911 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5081912 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term516 A B t b s a f g) = (term516 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081911 B) (@lem5081910 A B t b s a f g)). Qed.
Lemma lem5081913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5081914 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term643 A B t b s a f g) = (term643 A B t b s a f g).
Proof. exact (MK_COMB (@lem5081913) (@lem5081912 A B t b s a f g)). Qed.
Lemma lem5081915 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term916 A B x a b t s f g y) = (term916 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5081914 A B t b s a f g) (@lem5081860 A B x a b t s f g y)). Qed.
Lemma lem5081964 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term510 A B s a t b g f x).
Proof. exact (eq_refl (term510 A B s a t b g f x)). Qed.
Lemma lem5081965 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term511 A B s a t b g f) = (term511 A B s a t b g f).
Proof. exact (fun_ext (fun x : A => @lem5081964 A B s a t b g f x)). Qed.
Lemma lem5081966 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5081967 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term512 A B s a t b g f) = (term512 A B s a t b g f).
Proof. exact (MK_COMB (@lem5081966 A) (@lem5081965 A B s a t b g f)). Qed.
Lemma lem5081968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5081969 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (g : B -> A) (f : A -> B) : (term647 A B s a t b g f) = (term647 A B s a t b g f).
Proof. exact (MK_COMB (@lem5081968) (@lem5081967 A B s a t b g f)). Qed.
Lemma lem5081970 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term943 A B x a b t s f g y) = (term943 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5081969 A B s a t b g f) (@lem5081915 A B x a b t s f g y)). Qed.
Lemma lem5081977 {B : Type'} (b : B) (t : B -> Prop) : (term402 B b t) = (term402 B b t).
Proof. exact (eq_refl (term402 B b t)). Qed.
Lemma lem5081978 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term970 A B x a b t s f g y) = (term970 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5081977 B b t) (@lem5081970 A B x a b t s f g y)). Qed.
Lemma lem5081985 {A : Type'} (a : A) (s : A -> Prop) : (term402 A a s) = (term402 A a s).
Proof. exact (eq_refl (term402 A a s)). Qed.
Lemma lem5081986 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term997 A B x a b t s f g y) = (term997 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5081985 A a s) (@lem5081978 A B x a b t s f g y)). Qed.
Lemma lem5081997 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term657 A B s t) = (term657 A B s t).
Proof. exact (eq_refl (term657 A B s t)). Qed.
Lemma lem5081998 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1024 A B x a b t s f g y) = (term1024 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5081997 A B s t) (@lem5081986 A B x a b t s f g y)). Qed.
Lemma lem5082003 {B : Type'} (t : B -> Prop) : (term661 B t) = (term661 B t).
Proof. exact (eq_refl (term661 B t)). Qed.
Lemma lem5082004 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1051 A B x a b t s f g y) = (term1051 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5082003 B t) (@lem5081998 A B x a b t s f g y)). Qed.
Lemma lem5082009 {A : Type'} (s : A -> Prop) : (term661 A s) = (term661 A s).
Proof. exact (eq_refl (term661 A s)). Qed.
Lemma lem5082010 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1092 A B x a b t s f g y) = (term1092 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5082009 A s) (@lem5082004 A B x a b t s f g y)). Qed.
Lemma lem5082017 {A : Type'} (a : A) : (term701 A a) = (term701 A a).
Proof. exact (eq_refl (term701 A a)). Qed.
Lemma lem5082018 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1177 A B x a b t s f g y) = (term1177 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5082017 A a) (@lem5082010 A B x a b t s f g y)). Qed.
Lemma lem5082019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5082020 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term1349 A B x a b t s f g y) = (term1349 A B x a b t s f g y).
Proof. exact (MK_COMB (@lem5082019) (@lem5082018 A B x a b t s f g y)). Qed.
Lemma lem5082021 {A B : Type'} (x : A) (y : B) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) : (term1351 A B x y t b s a f g) = (term1351 A B x y t b s a f g).
Proof. exact (MK_COMB (@lem5082020 A B x a b t s f g y) (@lem5081507 A B t b s a f g)). Qed.
Lemma lem5082022 {A B : Type'} (x : A) (y : B) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1351 A B x y t b s a f g) : term1351 A B x y t b s a f g.
Proof. exact (EQ_MP (@lem5082021 A B x y t b s a f g) (@lem5081350 A B x y t b s a f g h1)). Qed.
Lemma lem5082023 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1177 A B x a b t s f g y.
Proof. exact (h1). Qed.
Lemma lem5082024 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1238 A B t b s a f g) : term1238 A B t b s a f g.
Proof. exact (h1). Qed.
Lemma lem5082025 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1092 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082023 A B x a b t s f g y h1)). Qed.
Lemma lem5082027 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1051 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082025 A B x a b t s f g y h1)). Qed.
Lemma lem5082029 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1024 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082027 A B x a b t s f g y h1)). Qed.
Lemma lem5082031 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term997 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082029 A B x a b t s f g y h1)). Qed.
Lemma lem5082033 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term970 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082031 A B x a b t s f g y h1)). Qed.
Lemma lem5082035 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term943 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082033 A B x a b t s f g y h1)). Qed.
Lemma lem5082037 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term916 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082035 A B x a b t s f g y h1)). Qed.
Lemma lem5082038 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term512 A B s a t b g f.
Proof. exact (proj1 (@lem5082035 A B x a b t s f g y h1)). Qed.
Lemma lem5082039 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term889 A B x a b t s f g y.
Proof. exact (proj2 (@lem5082037 A B x a b t s f g y h1)). Qed.
Lemma lem5082040 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term516 A B t b s a f g.
Proof. exact (proj1 (@lem5082037 A B x a b t s f g y h1)). Qed.
Lemma lem5082041 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term566 A B b a s t g f x) : term566 A B b a s t g f x.
Proof. exact (h1). Qed.
Lemma lem5082042 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term626 A B a b t s f g y) : term626 A B a b t s f g y.
Proof. exact (h1). Qed.
Lemma lem5082043 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : term545 A B b s f t a x.
Proof. exact (h1). Qed.
Lemma lem5082044 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term561 A B b a s t g f x) : term561 A B b a s t g f x.
Proof. exact (h1). Qed.
Lemma lem5082045 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : term540 A B b s f t a x.
Proof. exact (proj2 (@lem5082043 A B b s f t a x h1)). Qed.
Lemma lem5082047 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : term526 A B s b t a x.
Proof. exact (h1). Qed.
Lemma lem5082048 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : term535 A B s f t a x.
Proof. exact (h1). Qed.
Lemma lem5082049 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : term521 A B s b t a x.
Proof. exact (proj2 (@lem5082047 A B s b t a x h1)). Qed.
Lemma lem5082051 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : term519 A B b t a x.
Proof. exact (proj2 (@lem5082049 A B s b t a x h1)). Qed.
Lemma lem5082055 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : term531 A B s f t a x.
Proof. exact (proj2 (@lem5082048 A B s f t a x h1)). Qed.
Lemma lem5082057 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : term529 A B f t a x.
Proof. exact (proj2 (@lem5082055 A B s f t a x h1)). Qed.
Lemma lem5082061 {A B : Type'} (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term561 A B b a s t g f x) : term557 A B b a s t g f x.
Proof. exact (proj2 (@lem5082044 A B b a s t g f x h1)). Qed.
Lemma lem5082063 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : term526 A B s b t a x.
Proof. exact (h1). Qed.
Lemma lem5082064 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term554 A B a s t g f x.
Proof. exact (h1). Qed.
Lemma lem5082065 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : term521 A B s b t a x.
Proof. exact (proj2 (@lem5082063 A B s b t a x h1)). Qed.
Lemma lem5082067 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : term519 A B b t a x.
Proof. exact (proj2 (@lem5082065 A B s b t a x h1)). Qed.
Lemma lem5082071 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term551 A B s t g f x.
Proof. exact (proj2 (@lem5082064 A B a s t g f x h1)). Qed.
Lemma lem5082073 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term549 A B t g f x.
Proof. exact (proj2 (@lem5082071 A B a s t g f x h1)). Qed.
Lemma lem5082077 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : term605 A B a t g s b y.
Proof. exact (h1). Qed.
Lemma lem5082078 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term621 A B a b t s f g y) : term621 A B a b t s f g y.
Proof. exact (h1). Qed.
Lemma lem5082079 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : term599 A B a t g s b y.
Proof. exact (proj2 (@lem5082077 A B a t g s b y h1)). Qed.
Lemma lem5082081 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : term586 A B t a s b y.
Proof. exact (h1). Qed.
Lemma lem5082082 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : term594 A B t g s b y.
Proof. exact (h1). Qed.
Lemma lem5082083 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : term583 A B t a s b y.
Proof. exact (proj2 (@lem5082081 A B t a s b y h1)). Qed.
Lemma lem5082085 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : term581 A B a s b y.
Proof. exact (proj2 (@lem5082083 A B t a s b y h1)). Qed.
Lemma lem5082089 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : term591 A B t g s b y.
Proof. exact (proj2 (@lem5082082 A B t g s b y h1)). Qed.
Lemma lem5082091 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : term589 A B g s b y.
Proof. exact (proj2 (@lem5082089 A B t g s b y h1)). Qed.
Lemma lem5082095 {A B : Type'} (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term621 A B a b t s f g y) : term617 A B a b t s f g y.
Proof. exact (proj2 (@lem5082078 A B a b t s f g y h1)). Qed.
Lemma lem5082097 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : term586 A B t a s b y.
Proof. exact (h1). Qed.
Lemma lem5082098 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term614 A B b t s f g y.
Proof. exact (h1). Qed.
Lemma lem5082099 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : term583 A B t a s b y.
Proof. exact (proj2 (@lem5082097 A B t a s b y h1)). Qed.
Lemma lem5082101 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : term581 A B a s b y.
Proof. exact (proj2 (@lem5082099 A B t a s b y h1)). Qed.
Lemma lem5082105 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term611 A B t s f g y.
Proof. exact (proj2 (@lem5082098 A B b t s f g y h1)). Qed.
Lemma lem5082107 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term609 A B s f g y.
Proof. exact (proj2 (@lem5082105 A B b t s f g y h1)). Qed.
Lemma lem5082242 {B : Type'} (b : B) (t : B -> Prop) (h1 : term1365 B b t) : term1365 B b t.
Proof. exact (h1). Qed.
Lemma lem5082360 {A : Type'} (a : A) (x : A) (h1 : term506 A a x) : term506 A a x.
Proof. exact (h1). Qed.
Lemma lem5082478 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term1366 A B f x t) : term1366 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5082523 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term1367 A B t b s a g f x).
Proof. exact (@lem19490 (term97 A B t f x b) (term504 A s x a) ((term100 A B g f x) = x)). Qed.
Lemma lem5082524 {A B : Type'} (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term1368 A B s a g f x) = (term1368 A B s a g f x).
Proof. exact (eq_refl (term1368 A B s a g f x)). Qed.
Lemma lem5082531 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (f : A -> B) (x : A) (b : B) : (term1369 A B s a t f x b) = (term1370 A B t s a f x b).
Proof. exact (@lem19490 (term434 A B f x t) (term504 A s x a) (term547 A B f x b)). Qed.
Lemma lem5082532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5082533 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (f : A -> B) (x : A) (b : B) : (term1371 A B s a t f x b) = (term1372 A B t s a f x b).
Proof. exact (MK_COMB (@lem5082532) (@lem5082531 A B t s a f x b)). Qed.
Lemma lem5082534 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term1367 A B t b s a g f x) = (term1373 A B t b s a g f x).
Proof. exact (MK_COMB (@lem5082533 A B t s a f x b) (@lem5082524 A B s a g f x)). Qed.
Lemma lem5082536 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term1373 A B t b s a g f x).
Proof. exact (TRANS (@lem5082523 A B t b s a g f x) (@lem5082534 A B t b s a g f x)). Qed.
Lemma lem5082537 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) : (term511 A B s a t b g f) = (term1374 A B t b s a g f).
Proof. exact (fun_ext (fun x : A => @lem5082536 A B t b s a g f x)). Qed.
Lemma lem5082538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5082540 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) : (term512 A B s a t b g f) = (term1375 A B t b s a g f).
Proof. exact (MK_COMB (@lem5082538 A) (@lem5082537 A B t b s a g f)). Qed.
Lemma lem5082541 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1375 A B t b s a g f.
Proof. exact (EQ_MP (@lem5082540 A B t b s a g f) (@lem5082038 A B x a b t s f g y h1)). Qed.
Lemma lem5082714 {B : Type'} (b : B) (t : B -> Prop) (h1 : term1365 B b t) : term1365 B b t.
Proof. exact (h1). Qed.
Lemma lem5082832 {A : Type'} (a : A) (x : A) (h1 : term506 A a x) : term506 A a x.
Proof. exact (h1). Qed.
Lemma lem5082877 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term1367 A B t b s a g f x).
Proof. exact (@lem19490 (term97 A B t f x b) (term504 A s x a) ((term100 A B g f x) = x)). Qed.
Lemma lem5082878 {A B : Type'} (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term1368 A B s a g f x) = (term1368 A B s a g f x).
Proof. exact (eq_refl (term1368 A B s a g f x)). Qed.
Lemma lem5082885 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (f : A -> B) (x : A) (b : B) : (term1369 A B s a t f x b) = (term1370 A B t s a f x b).
Proof. exact (@lem19490 (term434 A B f x t) (term504 A s x a) (term547 A B f x b)). Qed.
Lemma lem5082886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5082887 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (f : A -> B) (x : A) (b : B) : (term1371 A B s a t f x b) = (term1372 A B t s a f x b).
Proof. exact (MK_COMB (@lem5082886) (@lem5082885 A B t s a f x b)). Qed.
Lemma lem5082888 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term1367 A B t b s a g f x) = (term1373 A B t b s a g f x).
Proof. exact (MK_COMB (@lem5082887 A B t s a f x b) (@lem5082878 A B s a g f x)). Qed.
Lemma lem5082890 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term1373 A B t b s a g f x).
Proof. exact (TRANS (@lem5082877 A B t b s a g f x) (@lem5082888 A B t b s a g f x)). Qed.
Lemma lem5082891 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) : (term511 A B s a t b g f) = (term1374 A B t b s a g f).
Proof. exact (fun_ext (fun x : A => @lem5082890 A B t b s a g f x)). Qed.
Lemma lem5082892 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5082894 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) : (term512 A B s a t b g f) = (term1375 A B t b s a g f).
Proof. exact (MK_COMB (@lem5082892 A) (@lem5082891 A B t b s a g f)). Qed.
Lemma lem5082895 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1375 A B t b s a g f.
Proof. exact (EQ_MP (@lem5082894 A B t b s a g f) (@lem5082038 A B x a b t s f g y h1)). Qed.
Lemma lem5082950 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term1366 A B f x t) : term1366 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5082995 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term1367 A B t b s a g f x).
Proof. exact (@lem19490 (term97 A B t f x b) (term504 A s x a) ((term100 A B g f x) = x)). Qed.
Lemma lem5082996 {A B : Type'} (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term1368 A B s a g f x) = (term1368 A B s a g f x).
Proof. exact (eq_refl (term1368 A B s a g f x)). Qed.
Lemma lem5083003 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (f : A -> B) (x : A) (b : B) : (term1369 A B s a t f x b) = (term1370 A B t s a f x b).
Proof. exact (@lem19490 (term434 A B f x t) (term504 A s x a) (term547 A B f x b)). Qed.
Lemma lem5083004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5083005 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (a : A) (f : A -> B) (x : A) (b : B) : (term1371 A B s a t f x b) = (term1372 A B t s a f x b).
Proof. exact (MK_COMB (@lem5083004) (@lem5083003 A B t s a f x b)). Qed.
Lemma lem5083006 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term1367 A B t b s a g f x) = (term1373 A B t b s a g f x).
Proof. exact (MK_COMB (@lem5083005 A B t s a f x b) (@lem5082996 A B s a g f x)). Qed.
Lemma lem5083008 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (x : A) : (term510 A B s a t b g f x) = (term1373 A B t b s a g f x).
Proof. exact (TRANS (@lem5082995 A B t b s a g f x) (@lem5083006 A B t b s a g f x)). Qed.
Lemma lem5083009 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) : (term511 A B s a t b g f) = (term1374 A B t b s a g f).
Proof. exact (fun_ext (fun x : A => @lem5083008 A B t b s a g f x)). Qed.
Lemma lem5083010 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5083012 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) : (term512 A B s a t b g f) = (term1375 A B t b s a g f).
Proof. exact (MK_COMB (@lem5083010 A) (@lem5083009 A B t b s a g f)). Qed.
Lemma lem5083013 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1375 A B t b s a g f.
Proof. exact (EQ_MP (@lem5083012 A B t b s a g f) (@lem5082038 A B x a b t s f g y h1)). Qed.
Lemma lem5083068 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term1376 A B g f x) : term1376 A B g f x.
Proof. exact (h1). Qed.
Lemma lem5083186 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1365 A a s) : term1365 A a s.
Proof. exact (h1). Qed.
Lemma lem5083304 {B : Type'} (b : B) (y : B) (h1 : term506 B b y) : term506 B b y.
Proof. exact (h1). Qed.
Lemma lem5083422 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term1377 A B g y s) : term1377 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5083506 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term1378 A B s a t b f g y).
Proof. exact (@lem19490 (term121 A B s g y a) (term504 B t y b) ((term124 A B f g y) = y)). Qed.
Lemma lem5083507 {A B : Type'} (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term1379 A B t b f g y) = (term1379 A B t b f g y).
Proof. exact (eq_refl (term1379 A B t b f g y)). Qed.
Lemma lem5083514 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (g : B -> A) (y : B) (a : A) : (term1380 A B t b s g y a) = (term1381 A B s t b g y a).
Proof. exact (@lem19490 (term392 A B g y s) (term504 B t y b) (term607 A B g y a)). Qed.
Lemma lem5083515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5083516 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (g : B -> A) (y : B) (a : A) : (term1382 A B t b s g y a) = (term1383 A B s t b g y a).
Proof. exact (MK_COMB (@lem5083515) (@lem5083514 A B s t b g y a)). Qed.
Lemma lem5083517 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term1378 A B s a t b f g y) = (term1384 A B s a t b f g y).
Proof. exact (MK_COMB (@lem5083516 A B s t b g y a) (@lem5083507 A B t b f g y)). Qed.
Lemma lem5083519 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term1384 A B s a t b f g y).
Proof. exact (TRANS (@lem5083506 A B s a t b f g y) (@lem5083517 A B s a t b f g y)). Qed.
Lemma lem5083520 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) : (term515 A B t b s a f g) = (term1385 A B s a t b f g).
Proof. exact (fun_ext (fun y : B => @lem5083519 A B s a t b f g y)). Qed.
Lemma lem5083521 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5083523 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) : (term516 A B t b s a f g) = (term1386 A B s a t b f g).
Proof. exact (MK_COMB (@lem5083521 B) (@lem5083520 A B s a t b f g)). Qed.
Lemma lem5083524 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1386 A B s a t b f g.
Proof. exact (EQ_MP (@lem5083523 A B s a t b f g) (@lem5082040 A B x a b t s f g y h1)). Qed.
Lemma lem5083658 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1365 A a s) : term1365 A a s.
Proof. exact (h1). Qed.
Lemma lem5083776 {B : Type'} (b : B) (y : B) (h1 : term506 B b y) : term506 B b y.
Proof. exact (h1). Qed.
Lemma lem5083860 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term1378 A B s a t b f g y).
Proof. exact (@lem19490 (term121 A B s g y a) (term504 B t y b) ((term124 A B f g y) = y)). Qed.
Lemma lem5083861 {A B : Type'} (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term1379 A B t b f g y) = (term1379 A B t b f g y).
Proof. exact (eq_refl (term1379 A B t b f g y)). Qed.
Lemma lem5083868 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (g : B -> A) (y : B) (a : A) : (term1380 A B t b s g y a) = (term1381 A B s t b g y a).
Proof. exact (@lem19490 (term392 A B g y s) (term504 B t y b) (term607 A B g y a)). Qed.
Lemma lem5083869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5083870 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (g : B -> A) (y : B) (a : A) : (term1382 A B t b s g y a) = (term1383 A B s t b g y a).
Proof. exact (MK_COMB (@lem5083869) (@lem5083868 A B s t b g y a)). Qed.
Lemma lem5083871 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term1378 A B s a t b f g y) = (term1384 A B s a t b f g y).
Proof. exact (MK_COMB (@lem5083870 A B s t b g y a) (@lem5083861 A B t b f g y)). Qed.
Lemma lem5083873 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term1384 A B s a t b f g y).
Proof. exact (TRANS (@lem5083860 A B s a t b f g y) (@lem5083871 A B s a t b f g y)). Qed.
Lemma lem5083874 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) : (term515 A B t b s a f g) = (term1385 A B s a t b f g).
Proof. exact (fun_ext (fun y : B => @lem5083873 A B s a t b f g y)). Qed.
Lemma lem5083875 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5083877 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) : (term516 A B t b s a f g) = (term1386 A B s a t b f g).
Proof. exact (MK_COMB (@lem5083875 B) (@lem5083874 A B s a t b f g)). Qed.
Lemma lem5083878 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1386 A B s a t b f g.
Proof. exact (EQ_MP (@lem5083877 A B s a t b f g) (@lem5082040 A B x a b t s f g y h1)). Qed.
Lemma lem5083894 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term1377 A B g y s) : term1377 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5083978 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term1378 A B s a t b f g y).
Proof. exact (@lem19490 (term121 A B s g y a) (term504 B t y b) ((term124 A B f g y) = y)). Qed.
Lemma lem5083979 {A B : Type'} (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term1379 A B t b f g y) = (term1379 A B t b f g y).
Proof. exact (eq_refl (term1379 A B t b f g y)). Qed.
Lemma lem5083986 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (g : B -> A) (y : B) (a : A) : (term1380 A B t b s g y a) = (term1381 A B s t b g y a).
Proof. exact (@lem19490 (term392 A B g y s) (term504 B t y b) (term607 A B g y a)). Qed.
Lemma lem5083987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5083988 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (b : B) (g : B -> A) (y : B) (a : A) : (term1382 A B t b s g y a) = (term1383 A B s t b g y a).
Proof. exact (MK_COMB (@lem5083987) (@lem5083986 A B s t b g y a)). Qed.
Lemma lem5083989 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term1378 A B s a t b f g y) = (term1384 A B s a t b f g y).
Proof. exact (MK_COMB (@lem5083988 A B s t b g y a) (@lem5083979 A B t b f g y)). Qed.
Lemma lem5083991 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (y : B) : (term514 A B t b s a f g y) = (term1384 A B s a t b f g y).
Proof. exact (TRANS (@lem5083978 A B s a t b f g y) (@lem5083989 A B s a t b f g y)). Qed.
Lemma lem5083992 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) : (term515 A B t b s a f g) = (term1385 A B s a t b f g).
Proof. exact (fun_ext (fun y : B => @lem5083991 A B s a t b f g y)). Qed.
Lemma lem5083993 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5083995 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) : (term516 A B t b s a f g) = (term1386 A B s a t b f g).
Proof. exact (MK_COMB (@lem5083993 B) (@lem5083992 A B s a t b f g)). Qed.
Lemma lem5083996 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1386 A B s a t b f g.
Proof. exact (EQ_MP (@lem5083995 A B s a t b f g) (@lem5082040 A B x a b t s f g y h1)). Qed.
Lemma lem5084012 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) : term1387 A B f g y.
Proof. exact (h1). Qed.
Lemma lem5084133 {A B : Type'} (_65360 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1388 A B t b s a g f _65360.
Proof. exact (@lem5082541 A B x a b t s f g y h1 _65360). Qed.
Lemma lem5084134 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (_65360 : A) : (term1388 A B t b s a g f _65360) = (term1373 A B t b s a g f _65360).
Proof. exact (eq_refl (term1388 A B t b s a g f _65360)). Qed.
Lemma lem5084135 {A B : Type'} (_65360 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1373 A B t b s a g f _65360.
Proof. exact (EQ_MP (@lem5084134 A B t b s a g f _65360) (@lem5084133 A B _65360 x a b t s f g y h1)). Qed.
Lemma lem5084151 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1388 A B t b s a g f _65366.
Proof. exact (@lem5082895 A B x a b t s f g y h1 _65366). Qed.
Lemma lem5084152 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (_65366 : A) : (term1388 A B t b s a g f _65366) = (term1373 A B t b s a g f _65366).
Proof. exact (eq_refl (term1388 A B t b s a g f _65366)). Qed.
Lemma lem5084153 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1373 A B t b s a g f _65366.
Proof. exact (EQ_MP (@lem5084152 A B t b s a g f _65366) (@lem5084151 A B _65366 x a b t s f g y h1)). Qed.
Lemma lem5084157 {A B : Type'} (_65368 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1388 A B t b s a g f _65368.
Proof. exact (@lem5083013 A B x a b t s f g y h1 _65368). Qed.
Lemma lem5084158 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (_65368 : A) : (term1388 A B t b s a g f _65368) = (term1373 A B t b s a g f _65368).
Proof. exact (eq_refl (term1388 A B t b s a g f _65368)). Qed.
Lemma lem5084159 {A B : Type'} (_65368 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1373 A B t b s a g f _65368.
Proof. exact (EQ_MP (@lem5084158 A B t b s a g f _65368) (@lem5084157 A B _65368 x a b t s f g y h1)). Qed.
Lemma lem5084184 {A B : Type'} (_65377 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1389 A B s a t b f g _65377.
Proof. exact (@lem5083524 A B x a b t s f g y h1 _65377). Qed.
Lemma lem5084185 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (_65377 : B) : (term1389 A B s a t b f g _65377) = (term1384 A B s a t b f g _65377).
Proof. exact (eq_refl (term1389 A B s a t b f g _65377)). Qed.
Lemma lem5084186 {A B : Type'} (_65377 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1384 A B s a t b f g _65377.
Proof. exact (EQ_MP (@lem5084185 A B s a t b f g _65377) (@lem5084184 A B _65377 x a b t s f g y h1)). Qed.
Lemma lem5084202 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1389 A B s a t b f g _65383.
Proof. exact (@lem5083878 A B x a b t s f g y h1 _65383). Qed.
Lemma lem5084203 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (_65383 : B) : (term1389 A B s a t b f g _65383) = (term1384 A B s a t b f g _65383).
Proof. exact (eq_refl (term1389 A B s a t b f g _65383)). Qed.
Lemma lem5084204 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1384 A B s a t b f g _65383.
Proof. exact (EQ_MP (@lem5084203 A B s a t b f g _65383) (@lem5084202 A B _65383 x a b t s f g y h1)). Qed.
Lemma lem5084208 {A B : Type'} (_65385 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1389 A B s a t b f g _65385.
Proof. exact (@lem5083996 A B x a b t s f g y h1 _65385). Qed.
Lemma lem5084209 {A B : Type'} (s : A -> Prop) (a : A) (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (_65385 : B) : (term1389 A B s a t b f g _65385) = (term1384 A B s a t b f g _65385).
Proof. exact (eq_refl (term1389 A B s a t b f g _65385)). Qed.
Lemma lem5084210 {A B : Type'} (_65385 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1384 A B s a t b f g _65385.
Proof. exact (EQ_MP (@lem5084209 A B s a t b f g _65385) (@lem5084208 A B _65385 x a b t s f g y h1)). Qed.
Lemma lem5084246 {A B : Type'} (_65360 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1370 A B t s a f _65360 b.
Proof. exact (proj1 (@lem5084135 A B _65360 x a b t s f g y h1)). Qed.
Lemma lem5084247 {A B : Type'} (_65360 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1390 A B s a f _65360 b.
Proof. exact (proj2 (@lem5084246 A B _65360 x a b t s f g y h1)). Qed.
Lemma lem5084270 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1370 A B t s a f _65366 b.
Proof. exact (proj1 (@lem5084153 A B _65366 x a b t s f g y h1)). Qed.
Lemma lem5084272 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1391 A B s a f _65366 t.
Proof. exact (proj1 (@lem5084270 A B _65366 x a b t s f g y h1)). Qed.
Lemma lem5084277 {A B : Type'} (_65368 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1368 A B s a g f _65368.
Proof. exact (proj2 (@lem5084159 A B _65368 x a b t s f g y h1)). Qed.
Lemma lem5084306 {A B : Type'} (_65377 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1381 A B s t b g _65377 a.
Proof. exact (proj1 (@lem5084186 A B _65377 x a b t s f g y h1)). Qed.
Lemma lem5084307 {A B : Type'} (_65377 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1392 A B t b g _65377 a.
Proof. exact (proj2 (@lem5084306 A B _65377 x a b t s f g y h1)). Qed.
Lemma lem5084330 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1381 A B s t b g _65383 a.
Proof. exact (proj1 (@lem5084204 A B _65383 x a b t s f g y h1)). Qed.
Lemma lem5084332 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1393 A B t b g _65383 s.
Proof. exact (proj1 (@lem5084330 A B _65383 x a b t s f g y h1)). Qed.
Lemma lem5084337 {A B : Type'} (_65385 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1379 A B t b f g _65385.
Proof. exact (proj2 (@lem5084210 A B _65385 x a b t s f g y h1)). Qed.
Lemma lem5084366 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : (f x) = b.
Proof. exact (proj1 (@lem5082043 A B b s f t a x h1)). Qed.
Lemma lem5084368 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : x = a.
Proof. exact (proj1 (@lem5082047 A B s b t a x h1)). Qed.
Lemma lem5084372 {B : Type'} (b : B) (t : B -> Prop) (h1 : term1365 B b t) : term1365 B b t.
Proof. exact (h1). Qed.
Lemma lem5084460 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : x = a.
Proof. exact (proj1 (@lem5082047 A B s b t a x h1)). Qed.
Lemma lem5084464 {A : Type'} (a : A) (x : A) (h1 : term506 A a x) : term506 A a x.
Proof. exact (h1). Qed.
Lemma lem5084548 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN B b t.
Proof. exact (proj1 (@lem5082033 A B x a b t s f g y h1)). Qed.
Lemma lem5084550 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : (f x) = b.
Proof. exact (proj1 (@lem5082043 A B b s f t a x h1)). Qed.
Lemma lem5084556 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term1366 A B f x t) : term1366 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5084642 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : (f x) = b.
Proof. exact (proj1 (@lem5082043 A B b s f t a x h1)). Qed.
Lemma lem5084719 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65360 : A) (b : B) : (term1390 A B s a f _65360 b) = (term1394 A B s a f _65360 b).
Proof. exact (@lem5073227 (term1365 A _65360 s) (_65360 = a) (term547 A B f _65360 b)). Qed.
Lemma lem5084720 {A B : Type'} (_65360 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1394 A B s a f _65360 b.
Proof. exact (EQ_MP (@lem5084719 A B s a f _65360 b) (@lem5084247 A B _65360 x a b t s f g y h1)). Qed.
Lemma lem5084740 {B : Type'} (b : B) (t : B -> Prop) (h1 : term1365 B b t) : term1365 B b t.
Proof. exact (h1). Qed.
Lemma lem5084828 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : x = a.
Proof. exact (proj1 (@lem5082063 A B s b t a x h1)). Qed.
Lemma lem5084832 {A : Type'} (a : A) (x : A) (h1 : term506 A a x) : term506 A a x.
Proof. exact (h1). Qed.
Lemma lem5084924 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term1366 A B f x t) : term1366 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5084983 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65366 : A) (t : B -> Prop) : (term1391 A B s a f _65366 t) = (term1395 A B s a f _65366 t).
Proof. exact (@lem5073227 (term1365 A _65366 s) (_65366 = a) (term434 A B f _65366 t)). Qed.
Lemma lem5084984 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1395 A B s a f _65366 t.
Proof. exact (EQ_MP (@lem5084983 A B s a f _65366 t) (@lem5084272 A B _65366 x a b t s f g y h1)). Qed.
Lemma lem5085016 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term1376 A B g f x) : term1376 A B g f x.
Proof. exact (h1). Qed.
Lemma lem5085063 {A B : Type'} (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (_65368 : A) : (term1368 A B s a g f _65368) = (term1396 A B s a g f _65368).
Proof. exact (@lem5073227 (term1365 A _65368 s) (_65368 = a) ((term100 A B g f _65368) = _65368)). Qed.
Lemma lem5085064 {A B : Type'} (_65368 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1396 A B s a g f _65368.
Proof. exact (EQ_MP (@lem5085063 A B s a g f _65368) (@lem5084277 A B _65368 x a b t s f g y h1)). Qed.
Lemma lem5085102 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : (g y) = a.
Proof. exact (proj1 (@lem5082077 A B a t g s b y h1)). Qed.
Lemma lem5085104 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : y = b.
Proof. exact (proj1 (@lem5082081 A B t a s b y h1)). Qed.
Lemma lem5085108 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1365 A a s) : term1365 A a s.
Proof. exact (h1). Qed.
Lemma lem5085196 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : y = b.
Proof. exact (proj1 (@lem5082081 A B t a s b y h1)). Qed.
Lemma lem5085200 {B : Type'} (b : B) (y : B) (h1 : term506 B b y) : term506 B b y.
Proof. exact (h1). Qed.
Lemma lem5085282 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN A a s.
Proof. exact (proj1 (@lem5082031 A B x a b t s f g y h1)). Qed.
Lemma lem5085286 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : (g y) = a.
Proof. exact (proj1 (@lem5082077 A B a t g s b y h1)). Qed.
Lemma lem5085292 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term1377 A B g y s) : term1377 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5085378 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : (g y) = a.
Proof. exact (proj1 (@lem5082077 A B a t g s b y h1)). Qed.
Lemma lem5085419 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65377 : B) (a : A) : (term1392 A B t b g _65377 a) = (term1397 A B t b g _65377 a).
Proof. exact (@lem5073227 (term1365 B _65377 t) (_65377 = b) (term607 A B g _65377 a)). Qed.
Lemma lem5085420 {A B : Type'} (_65377 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1397 A B t b g _65377 a.
Proof. exact (EQ_MP (@lem5085419 A B t b g _65377 a) (@lem5084307 A B _65377 x a b t s f g y h1)). Qed.
Lemma lem5085476 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1365 A a s) : term1365 A a s.
Proof. exact (h1). Qed.
Lemma lem5085564 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : y = b.
Proof. exact (proj1 (@lem5082097 A B t a s b y h1)). Qed.
Lemma lem5085568 {B : Type'} (b : B) (y : B) (h1 : term506 B b y) : term506 B b y.
Proof. exact (h1). Qed.
Lemma lem5085660 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term1377 A B g y s) : term1377 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5085683 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65383 : B) (s : A -> Prop) : (term1393 A B t b g _65383 s) = (term1398 A B t b g _65383 s).
Proof. exact (@lem5073227 (term1365 B _65383 t) (_65383 = b) (term392 A B g _65383 s)). Qed.
Lemma lem5085684 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1398 A B t b g _65383 s.
Proof. exact (EQ_MP (@lem5085683 A B t b g _65383 s) (@lem5084332 A B _65383 x a b t s f g y h1)). Qed.
Lemma lem5085752 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) : term1387 A B f g y.
Proof. exact (h1). Qed.
Lemma lem5085763 {A B : Type'} (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (_65385 : B) : (term1379 A B t b f g _65385) = (term1399 A B t b f g _65385).
Proof. exact (@lem5073227 (term1365 B _65385 t) (_65385 = b) ((term124 A B f g _65385) = _65385)). Qed.
Lemma lem5085764 {A B : Type'} (_65385 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1399 A B t b f g _65385.
Proof. exact (EQ_MP (@lem5085763 A B t b f g _65385) (@lem5084337 A B _65385 x a b t s f g y h1)). Qed.
Lemma lem5085826 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1238 A B t b s a f g) : term705 A a.
Proof. exact (proj1 (@lem5082024 A B t b s a f g h1)). Qed.
Lemma lem5086006 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN B b t.
Proof. exact (proj1 (@lem5082033 A B x a b t s f g y h1)). Qed.
Lemma lem5086007 {A B : Type'} (f : A -> B) (b : B) : (term1400 A B f b) = (term1400 A B f b).
Proof. exact (eq_refl (term1400 A B f b)). Qed.
Lemma lem5086008 {A B : Type'} (f : A -> B) (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : (term1401 A B f b x) = (term1401 A B f b a).
Proof. exact (MK_COMB (@lem5086007 A B f b) (@lem5084368 A B s b t a x h1)). Qed.
Lemma lem5086009 {A B : Type'} (f : A -> B) (a : A) (b : B) : (term1401 A B f b a) = ((f a) = b).
Proof. exact (eq_refl (term1401 A B f b a)). Qed.
Lemma lem5086010 {A B : Type'} (f : A -> B) (b : B) (x : A) : (term1402 A B f b x) = (term1402 A B f b x).
Proof. exact (eq_refl (term1402 A B f b x)). Qed.
Lemma lem5086011 {A B : Type'} (x : A) (f : A -> B) (a : A) (b : B) : ((term1401 A B f b x) = (term1401 A B f b a)) = ((term1401 A B f b x) = ((f a) = b)).
Proof. exact (MK_COMB (@lem5086010 A B f b x) (@lem5086009 A B f a b)). Qed.
Lemma lem5086012 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term1401 A B f b x) = ((f x) = b).
Proof. exact (eq_refl (term1401 A B f b x)). Qed.
Lemma lem5086013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5086014 {A B : Type'} (f : A -> B) (x : A) (b : B) : (term1402 A B f b x) = (term1403 A B f x b).
Proof. exact (MK_COMB (@lem5086013) (@lem5086012 A B f x b)). Qed.
Lemma lem5086015 {A B : Type'} (f : A -> B) (a : A) (b : B) : ((f a) = b) = ((f a) = b).
Proof. exact (eq_refl ((f a) = b)). Qed.
Lemma lem5086016 {A B : Type'} (x : A) (f : A -> B) (a : A) (b : B) : ((term1401 A B f b x) = ((f a) = b)) = (((f x) = b) = ((f a) = b)).
Proof. exact (MK_COMB (@lem5086014 A B f x b) (@lem5086015 A B f a b)). Qed.
Lemma lem5086017 {A B : Type'} (x : A) (f : A -> B) (a : A) (b : B) : ((term1401 A B f b x) = (term1401 A B f b a)) = (((f x) = b) = ((f a) = b)).
Proof. exact (TRANS (@lem5086011 A B x f a b) (@lem5086016 A B x f a b)). Qed.
Lemma lem5086018 {A B : Type'} (f : A -> B) (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : ((f x) = b) = ((f a) = b).
Proof. exact (EQ_MP (@lem5086017 A B x f a b) (@lem5086008 A B f s b t a x h1)). Qed.
Lemma lem5086019 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) (h2 : term545 A B b s f t a x) : (f a) = b.
Proof. exact (EQ_MP (@lem5086018 A B f s b t a x h1) (@lem5084366 A B b s f t a x h2)). Qed.
Lemma lem5086046 {B : Type'} (b : B) (t : B -> Prop) (h1 : term1365 B b t) : term1365 B b t.
Proof. exact (h1). Qed.
Lemma lem5086131 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) (h2 : term545 A B b s f t a x) : b = (f a).
Proof. exact (SYM (@lem5086019 A B b s f t a x h1 h2)). Qed.
Lemma lem5086216 {B : Type'} (t : B -> Prop) : (term1404 B t) = (term1404 B t).
Proof. exact (eq_refl (term1404 B t)). Qed.
Lemma lem5086217 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) (h2 : term545 A B b s f t a x) : (term1405 B t b) = (term1406 A B t f a).
Proof. exact (MK_COMB (@lem5086216 B t) (@lem5086131 A B b s f t a x h1 h2)). Qed.
Lemma lem5086218 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) : (term1406 A B t f a) = (term434 A B f a t).
Proof. exact (eq_refl (term1406 A B t f a)). Qed.
Lemma lem5086219 {B : Type'} (t : B -> Prop) (b : B) : (term1407 B t b) = (term1407 B t b).
Proof. exact (eq_refl (term1407 B t b)). Qed.
Lemma lem5086220 {A B : Type'} (b : B) (f : A -> B) (a : A) (t : B -> Prop) : ((term1405 B t b) = (term1406 A B t f a)) = ((term1405 B t b) = (term434 A B f a t)).
Proof. exact (MK_COMB (@lem5086219 B t b) (@lem5086218 A B f a t)). Qed.
Lemma lem5086221 {B : Type'} (b : B) (t : B -> Prop) : (term1405 B t b) = (@IN B b t).
Proof. exact (eq_refl (term1405 B t b)). Qed.
Lemma lem5086222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5086223 {B : Type'} (b : B) (t : B -> Prop) : (term1407 B t b) = (term1408 B b t).
Proof. exact (MK_COMB (@lem5086222) (@lem5086221 B b t)). Qed.
Lemma lem5086224 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) : (term434 A B f a t) = (term434 A B f a t).
Proof. exact (eq_refl (term434 A B f a t)). Qed.
Lemma lem5086225 {A B : Type'} (b : B) (f : A -> B) (a : A) (t : B -> Prop) : ((term1405 B t b) = (term434 A B f a t)) = ((@IN B b t) = (term434 A B f a t)).
Proof. exact (MK_COMB (@lem5086223 B b t) (@lem5086224 A B f a t)). Qed.
Lemma lem5086226 {A B : Type'} (b : B) (f : A -> B) (a : A) (t : B -> Prop) : ((term1405 B t b) = (term1406 A B t f a)) = ((@IN B b t) = (term434 A B f a t)).
Proof. exact (TRANS (@lem5086220 A B b f a t) (@lem5086225 A B b f a t)). Qed.
Lemma lem5086227 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) (h2 : term545 A B b s f t a x) : (@IN B b t) = (term434 A B f a t).
Proof. exact (EQ_MP (@lem5086226 A B b f a t) (@lem5086217 A B b s f t a x h1 h2)). Qed.
Lemma lem5086243 {B : Type'} (t : B -> Prop) : (term1409 B t) = (term1409 B t).
Proof. exact (eq_refl (term1409 B t)). Qed.
Lemma lem5086244 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) (h2 : term545 A B b s f t a x) : (term1410 B t b) = (term1411 A B t f a).
Proof. exact (MK_COMB (@lem5086243 B t) (@lem5086131 A B b s f t a x h1 h2)). Qed.
Lemma lem5086245 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) : (term1411 A B t f a) = (term1366 A B f a t).
Proof. exact (eq_refl (term1411 A B t f a)). Qed.
Lemma lem5086246 {B : Type'} (t : B -> Prop) (b : B) : (term1412 B t b) = (term1412 B t b).
Proof. exact (eq_refl (term1412 B t b)). Qed.
Lemma lem5086247 {A B : Type'} (b : B) (f : A -> B) (a : A) (t : B -> Prop) : ((term1410 B t b) = (term1411 A B t f a)) = ((term1410 B t b) = (term1366 A B f a t)).
Proof. exact (MK_COMB (@lem5086246 B t b) (@lem5086245 A B f a t)). Qed.
Lemma lem5086248 {B : Type'} (b : B) (t : B -> Prop) : (term1410 B t b) = (term1365 B b t).
Proof. exact (eq_refl (term1410 B t b)). Qed.
Lemma lem5086249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5086250 {B : Type'} (b : B) (t : B -> Prop) : (term1412 B t b) = (term1413 B b t).
Proof. exact (MK_COMB (@lem5086249) (@lem5086248 B b t)). Qed.
Lemma lem5086251 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) : (term1366 A B f a t) = (term1366 A B f a t).
Proof. exact (eq_refl (term1366 A B f a t)). Qed.
Lemma lem5086252 {A B : Type'} (b : B) (f : A -> B) (a : A) (t : B -> Prop) : ((term1410 B t b) = (term1366 A B f a t)) = ((term1365 B b t) = (term1366 A B f a t)).
Proof. exact (MK_COMB (@lem5086250 B b t) (@lem5086251 A B f a t)). Qed.
Lemma lem5086253 {A B : Type'} (b : B) (f : A -> B) (a : A) (t : B -> Prop) : ((term1410 B t b) = (term1411 A B t f a)) = ((term1365 B b t) = (term1366 A B f a t)).
Proof. exact (TRANS (@lem5086247 A B b f a t) (@lem5086252 A B b f a t)). Qed.
Lemma lem5086254 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) (h2 : term545 A B b s f t a x) : (term1365 B b t) = (term1366 A B f a t).
Proof. exact (EQ_MP (@lem5086253 A B b f a t) (@lem5086244 A B b s f t a x h1 h2)). Qed.
Lemma lem5086255 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term526 A B s b t a x) (h3 : term545 A B b s f t a x) : term1366 A B f a t.
Proof. exact (EQ_MP (@lem5086254 A B b s f t a x h2 h3) (@lem5086046 B b t h1)). Qed.
Lemma lem5086460 {A : Type'} (a : A) : (term1414 A a) = (term1414 A a).
Proof. exact (eq_refl (term1414 A a)). Qed.
Lemma lem5086461 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : (term1415 A a x) = (term1416 A a).
Proof. exact (MK_COMB (@lem5086460 A a) (@lem5084460 A B s b t a x h1)). Qed.
Lemma lem5086462 {A : Type'} (a : A) : (term1416 A a) = (term705 A a).
Proof. exact (eq_refl (term1416 A a)). Qed.
Lemma lem5086463 {A : Type'} (a : A) (x : A) : (term1417 A a x) = (term1417 A a x).
Proof. exact (eq_refl (term1417 A a x)). Qed.
Lemma lem5086464 {A : Type'} (x : A) (a : A) : ((term1415 A a x) = (term1416 A a)) = ((term1415 A a x) = (term705 A a)).
Proof. exact (MK_COMB (@lem5086463 A a x) (@lem5086462 A a)). Qed.
Lemma lem5086465 {A : Type'} (a : A) (x : A) : (term1415 A a x) = (term506 A a x).
Proof. exact (eq_refl (term1415 A a x)). Qed.
Lemma lem5086466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5086467 {A : Type'} (a : A) (x : A) : (term1417 A a x) = (term1418 A a x).
Proof. exact (MK_COMB (@lem5086466) (@lem5086465 A a x)). Qed.
Lemma lem5086468 {A : Type'} (a : A) : (term705 A a) = (term705 A a).
Proof. exact (eq_refl (term705 A a)). Qed.
Lemma lem5086469 {A : Type'} (x : A) (a : A) : ((term1415 A a x) = (term705 A a)) = ((term506 A a x) = (term705 A a)).
Proof. exact (MK_COMB (@lem5086467 A a x) (@lem5086468 A a)). Qed.
Lemma lem5086470 {A : Type'} (x : A) (a : A) : ((term1415 A a x) = (term1416 A a)) = ((term506 A a x) = (term705 A a)).
Proof. exact (TRANS (@lem5086464 A x a) (@lem5086469 A x a)). Qed.
Lemma lem5086471 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : (term506 A a x) = (term705 A a).
Proof. exact (EQ_MP (@lem5086470 A x a) (@lem5086461 A B s b t a x h1)). Qed.
Lemma lem5086682 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : term705 A a.
Proof. exact (EQ_MP (@lem5086471 A B s b t a x h2) (@lem5084464 A a x h1)). Qed.
Lemma lem5086763 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : b = (f x).
Proof. exact (SYM (@lem5084550 A B b s f t a x h1)). Qed.
Lemma lem5086848 {B : Type'} (t : B -> Prop) : (term1404 B t) = (term1404 B t).
Proof. exact (eq_refl (term1404 B t)). Qed.
Lemma lem5086849 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : (term1405 B t b) = (term1406 A B t f x).
Proof. exact (MK_COMB (@lem5086848 B t) (@lem5086763 A B b s f t a x h1)). Qed.
Lemma lem5086850 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term1406 A B t f x) = (term434 A B f x t).
Proof. exact (eq_refl (term1406 A B t f x)). Qed.
Lemma lem5086851 {B : Type'} (t : B -> Prop) (b : B) : (term1407 B t b) = (term1407 B t b).
Proof. exact (eq_refl (term1407 B t b)). Qed.
Lemma lem5086852 {A B : Type'} (b : B) (f : A -> B) (x : A) (t : B -> Prop) : ((term1405 B t b) = (term1406 A B t f x)) = ((term1405 B t b) = (term434 A B f x t)).
Proof. exact (MK_COMB (@lem5086851 B t b) (@lem5086850 A B f x t)). Qed.
Lemma lem5086853 {B : Type'} (b : B) (t : B -> Prop) : (term1405 B t b) = (@IN B b t).
Proof. exact (eq_refl (term1405 B t b)). Qed.
Lemma lem5086854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5086855 {B : Type'} (b : B) (t : B -> Prop) : (term1407 B t b) = (term1408 B b t).
Proof. exact (MK_COMB (@lem5086854) (@lem5086853 B b t)). Qed.
Lemma lem5086856 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term434 A B f x t) = (term434 A B f x t).
Proof. exact (eq_refl (term434 A B f x t)). Qed.
Lemma lem5086857 {A B : Type'} (b : B) (f : A -> B) (x : A) (t : B -> Prop) : ((term1405 B t b) = (term434 A B f x t)) = ((@IN B b t) = (term434 A B f x t)).
Proof. exact (MK_COMB (@lem5086855 B b t) (@lem5086856 A B f x t)). Qed.
Lemma lem5086858 {A B : Type'} (b : B) (f : A -> B) (x : A) (t : B -> Prop) : ((term1405 B t b) = (term1406 A B t f x)) = ((@IN B b t) = (term434 A B f x t)).
Proof. exact (TRANS (@lem5086852 A B b f x t) (@lem5086857 A B b f x t)). Qed.
Lemma lem5086859 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : (@IN B b t) = (term434 A B f x t).
Proof. exact (EQ_MP (@lem5086858 A B b f x t) (@lem5086849 A B b s f t a x h1)). Qed.
Lemma lem5086902 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term1366 A B f x t) : term1366 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5086983 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : b = (f x).
Proof. exact (SYM (@lem5084642 A B b s f t a x h1)). Qed.
Lemma lem5087094 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : term506 A x a.
Proof. exact (proj1 (@lem5082048 A B s f t a x h1)). Qed.
Lemma lem5087190 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65360 : A) : (term1419 A B s a f _65360) = (term1419 A B s a f _65360).
Proof. exact (eq_refl (term1419 A B s a f _65360)). Qed.
Lemma lem5087191 {A B : Type'} (_65360 : A) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : (term1420 A B s a f _65360 b) = (term1421 A B s a _65360 f x).
Proof. exact (MK_COMB (@lem5087190 A B s a f _65360) (@lem5086983 A B b s f t a x h1)). Qed.
Lemma lem5087192 {A B : Type'} (s : A -> Prop) (a : A) (_65360 : A) (f : A -> B) (x : A) : (term1421 A B s a _65360 f x) = (term1422 A B s a _65360 f x).
Proof. exact (eq_refl (term1421 A B s a _65360 f x)). Qed.
Lemma lem5087193 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65360 : A) (b : B) : (term1423 A B s a f _65360 b) = (term1423 A B s a f _65360 b).
Proof. exact (eq_refl (term1423 A B s a f _65360 b)). Qed.
Lemma lem5087194 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (_65360 : A) (f : A -> B) (x : A) : ((term1420 A B s a f _65360 b) = (term1421 A B s a _65360 f x)) = ((term1420 A B s a f _65360 b) = (term1422 A B s a _65360 f x)).
Proof. exact (MK_COMB (@lem5087193 A B s a f _65360 b) (@lem5087192 A B s a _65360 f x)). Qed.
Lemma lem5087195 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65360 : A) (b : B) : (term1420 A B s a f _65360 b) = (term1394 A B s a f _65360 b).
Proof. exact (eq_refl (term1420 A B s a f _65360 b)). Qed.
Lemma lem5087196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5087197 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65360 : A) (b : B) : (term1423 A B s a f _65360 b) = (term1424 A B s a f _65360 b).
Proof. exact (MK_COMB (@lem5087196) (@lem5087195 A B s a f _65360 b)). Qed.
Lemma lem5087198 {A B : Type'} (s : A -> Prop) (a : A) (_65360 : A) (f : A -> B) (x : A) : (term1422 A B s a _65360 f x) = (term1422 A B s a _65360 f x).
Proof. exact (eq_refl (term1422 A B s a _65360 f x)). Qed.
Lemma lem5087199 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (_65360 : A) (f : A -> B) (x : A) : ((term1420 A B s a f _65360 b) = (term1422 A B s a _65360 f x)) = ((term1394 A B s a f _65360 b) = (term1422 A B s a _65360 f x)).
Proof. exact (MK_COMB (@lem5087197 A B s a f _65360 b) (@lem5087198 A B s a _65360 f x)). Qed.
Lemma lem5087200 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (_65360 : A) (f : A -> B) (x : A) : ((term1420 A B s a f _65360 b) = (term1421 A B s a _65360 f x)) = ((term1394 A B s a f _65360 b) = (term1422 A B s a _65360 f x)).
Proof. exact (TRANS (@lem5087194 A B b s a _65360 f x) (@lem5087199 A B b s a _65360 f x)). Qed.
Lemma lem5087201 {A B : Type'} (_65360 : A) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term545 A B b s f t a x) : (term1394 A B s a f _65360 b) = (term1422 A B s a _65360 f x).
Proof. exact (EQ_MP (@lem5087200 A B b s a _65360 f x) (@lem5087191 A B _65360 b s f t a x h1)). Qed.
Lemma lem5087202 {A B : Type'} (_65360 : A) (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term1422 A B s a _65360 f x.
Proof. exact (EQ_MP (@lem5087201 A B _65360 b s f t a x h2) (@lem5084720 A B _65360 x a b t s f g y h1)). Qed.
Lemma lem5087340 {B : Type'} (b : B) (t : B -> Prop) (h1 : term1365 B b t) : term1365 B b t.
Proof. exact (h1). Qed.
Lemma lem5087549 {A : Type'} (a : A) : (term1414 A a) = (term1414 A a).
Proof. exact (eq_refl (term1414 A a)). Qed.
Lemma lem5087550 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : (term1415 A a x) = (term1416 A a).
Proof. exact (MK_COMB (@lem5087549 A a) (@lem5084828 A B s b t a x h1)). Qed.
Lemma lem5087551 {A : Type'} (a : A) : (term1416 A a) = (term705 A a).
Proof. exact (eq_refl (term1416 A a)). Qed.
Lemma lem5087552 {A : Type'} (a : A) (x : A) : (term1417 A a x) = (term1417 A a x).
Proof. exact (eq_refl (term1417 A a x)). Qed.
Lemma lem5087553 {A : Type'} (x : A) (a : A) : ((term1415 A a x) = (term1416 A a)) = ((term1415 A a x) = (term705 A a)).
Proof. exact (MK_COMB (@lem5087552 A a x) (@lem5087551 A a)). Qed.
Lemma lem5087554 {A : Type'} (a : A) (x : A) : (term1415 A a x) = (term506 A a x).
Proof. exact (eq_refl (term1415 A a x)). Qed.
Lemma lem5087555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5087556 {A : Type'} (a : A) (x : A) : (term1417 A a x) = (term1418 A a x).
Proof. exact (MK_COMB (@lem5087555) (@lem5087554 A a x)). Qed.
Lemma lem5087557 {A : Type'} (a : A) : (term705 A a) = (term705 A a).
Proof. exact (eq_refl (term705 A a)). Qed.
Lemma lem5087558 {A : Type'} (x : A) (a : A) : ((term1415 A a x) = (term705 A a)) = ((term506 A a x) = (term705 A a)).
Proof. exact (MK_COMB (@lem5087556 A a x) (@lem5087557 A a)). Qed.
Lemma lem5087559 {A : Type'} (x : A) (a : A) : ((term1415 A a x) = (term1416 A a)) = ((term506 A a x) = (term705 A a)).
Proof. exact (TRANS (@lem5087553 A x a) (@lem5087558 A x a)). Qed.
Lemma lem5087560 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term526 A B s b t a x) : (term506 A a x) = (term705 A a).
Proof. exact (EQ_MP (@lem5087559 A x a) (@lem5087550 A B s b t a x h1)). Qed.
Lemma lem5087561 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : term705 A a.
Proof. exact (EQ_MP (@lem5087560 A B s b t a x h2) (@lem5084832 A a x h1)). Qed.
Lemma lem5087729 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN A a s.
Proof. exact (proj1 (@lem5082031 A B x a b t s f g y h1)). Qed.
Lemma lem5087744 {A B : Type'} (g : B -> A) (a : A) : (term1425 A B g a) = (term1425 A B g a).
Proof. exact (eq_refl (term1425 A B g a)). Qed.
Lemma lem5087745 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : (term1426 A B g a y) = (term1426 A B g a b).
Proof. exact (MK_COMB (@lem5087744 A B g a) (@lem5085104 A B t a s b y h1)). Qed.
Lemma lem5087746 {A B : Type'} (g : B -> A) (b : B) (a : A) : (term1426 A B g a b) = ((g b) = a).
Proof. exact (eq_refl (term1426 A B g a b)). Qed.
Lemma lem5087747 {A B : Type'} (g : B -> A) (a : A) (y : B) : (term1427 A B g a y) = (term1427 A B g a y).
Proof. exact (eq_refl (term1427 A B g a y)). Qed.
Lemma lem5087748 {A B : Type'} (y : B) (g : B -> A) (b : B) (a : A) : ((term1426 A B g a y) = (term1426 A B g a b)) = ((term1426 A B g a y) = ((g b) = a)).
Proof. exact (MK_COMB (@lem5087747 A B g a y) (@lem5087746 A B g b a)). Qed.
Lemma lem5087749 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term1426 A B g a y) = ((g y) = a).
Proof. exact (eq_refl (term1426 A B g a y)). Qed.
Lemma lem5087750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5087751 {A B : Type'} (g : B -> A) (y : B) (a : A) : (term1427 A B g a y) = (term1428 A B g y a).
Proof. exact (MK_COMB (@lem5087750) (@lem5087749 A B g y a)). Qed.
Lemma lem5087752 {A B : Type'} (g : B -> A) (b : B) (a : A) : ((g b) = a) = ((g b) = a).
Proof. exact (eq_refl ((g b) = a)). Qed.
Lemma lem5087753 {A B : Type'} (y : B) (g : B -> A) (b : B) (a : A) : ((term1426 A B g a y) = ((g b) = a)) = (((g y) = a) = ((g b) = a)).
Proof. exact (MK_COMB (@lem5087751 A B g y a) (@lem5087752 A B g b a)). Qed.
Lemma lem5087754 {A B : Type'} (y : B) (g : B -> A) (b : B) (a : A) : ((term1426 A B g a y) = (term1426 A B g a b)) = (((g y) = a) = ((g b) = a)).
Proof. exact (TRANS (@lem5087748 A B y g b a) (@lem5087753 A B y g b a)). Qed.
Lemma lem5087755 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : ((g y) = a) = ((g b) = a).
Proof. exact (EQ_MP (@lem5087754 A B y g b a) (@lem5087745 A B g t a s b y h1)). Qed.
Lemma lem5087756 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) (h2 : term586 A B t a s b y) : (g b) = a.
Proof. exact (EQ_MP (@lem5087755 A B g t a s b y h2) (@lem5085102 A B a t g s b y h1)). Qed.
Lemma lem5087783 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1365 A a s) : term1365 A a s.
Proof. exact (h1). Qed.
Lemma lem5087868 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) (h2 : term586 A B t a s b y) : a = (g b).
Proof. exact (SYM (@lem5087756 A B g t a s b y h1 h2)). Qed.
Lemma lem5087938 {A : Type'} (s : A -> Prop) : (term1404 A s) = (term1404 A s).
Proof. exact (eq_refl (term1404 A s)). Qed.
Lemma lem5087939 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) (h2 : term586 A B t a s b y) : (term1405 A s a) = (term1429 A B s g b).
Proof. exact (MK_COMB (@lem5087938 A s) (@lem5087868 A B g t a s b y h1 h2)). Qed.
Lemma lem5087940 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) : (term1429 A B s g b) = (term392 A B g b s).
Proof. exact (eq_refl (term1429 A B s g b)). Qed.
Lemma lem5087941 {A : Type'} (s : A -> Prop) (a : A) : (term1407 A s a) = (term1407 A s a).
Proof. exact (eq_refl (term1407 A s a)). Qed.
Lemma lem5087942 {A B : Type'} (a : A) (g : B -> A) (b : B) (s : A -> Prop) : ((term1405 A s a) = (term1429 A B s g b)) = ((term1405 A s a) = (term392 A B g b s)).
Proof. exact (MK_COMB (@lem5087941 A s a) (@lem5087940 A B g b s)). Qed.
Lemma lem5087943 {A : Type'} (a : A) (s : A -> Prop) : (term1405 A s a) = (@IN A a s).
Proof. exact (eq_refl (term1405 A s a)). Qed.
Lemma lem5087944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5087945 {A : Type'} (a : A) (s : A -> Prop) : (term1407 A s a) = (term1408 A a s).
Proof. exact (MK_COMB (@lem5087944) (@lem5087943 A a s)). Qed.
Lemma lem5087946 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) : (term392 A B g b s) = (term392 A B g b s).
Proof. exact (eq_refl (term392 A B g b s)). Qed.
Lemma lem5087947 {A B : Type'} (a : A) (g : B -> A) (b : B) (s : A -> Prop) : ((term1405 A s a) = (term392 A B g b s)) = ((@IN A a s) = (term392 A B g b s)).
Proof. exact (MK_COMB (@lem5087945 A a s) (@lem5087946 A B g b s)). Qed.
Lemma lem5087948 {A B : Type'} (a : A) (g : B -> A) (b : B) (s : A -> Prop) : ((term1405 A s a) = (term1429 A B s g b)) = ((@IN A a s) = (term392 A B g b s)).
Proof. exact (TRANS (@lem5087942 A B a g b s) (@lem5087947 A B a g b s)). Qed.
Lemma lem5087949 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) (h2 : term586 A B t a s b y) : (@IN A a s) = (term392 A B g b s).
Proof. exact (EQ_MP (@lem5087948 A B a g b s) (@lem5087939 A B g t a s b y h1 h2)). Qed.
Lemma lem5087979 {A : Type'} (s : A -> Prop) : (term1409 A s) = (term1409 A s).
Proof. exact (eq_refl (term1409 A s)). Qed.
Lemma lem5087980 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) (h2 : term586 A B t a s b y) : (term1410 A s a) = (term1430 A B s g b).
Proof. exact (MK_COMB (@lem5087979 A s) (@lem5087868 A B g t a s b y h1 h2)). Qed.
Lemma lem5087981 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) : (term1430 A B s g b) = (term1377 A B g b s).
Proof. exact (eq_refl (term1430 A B s g b)). Qed.
Lemma lem5087982 {A : Type'} (s : A -> Prop) (a : A) : (term1412 A s a) = (term1412 A s a).
Proof. exact (eq_refl (term1412 A s a)). Qed.
Lemma lem5087983 {A B : Type'} (a : A) (g : B -> A) (b : B) (s : A -> Prop) : ((term1410 A s a) = (term1430 A B s g b)) = ((term1410 A s a) = (term1377 A B g b s)).
Proof. exact (MK_COMB (@lem5087982 A s a) (@lem5087981 A B g b s)). Qed.
Lemma lem5087984 {A : Type'} (a : A) (s : A -> Prop) : (term1410 A s a) = (term1365 A a s).
Proof. exact (eq_refl (term1410 A s a)). Qed.
Lemma lem5087985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5087986 {A : Type'} (a : A) (s : A -> Prop) : (term1412 A s a) = (term1413 A a s).
Proof. exact (MK_COMB (@lem5087985) (@lem5087984 A a s)). Qed.
Lemma lem5087987 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) : (term1377 A B g b s) = (term1377 A B g b s).
Proof. exact (eq_refl (term1377 A B g b s)). Qed.
Lemma lem5087988 {A B : Type'} (a : A) (g : B -> A) (b : B) (s : A -> Prop) : ((term1410 A s a) = (term1377 A B g b s)) = ((term1365 A a s) = (term1377 A B g b s)).
Proof. exact (MK_COMB (@lem5087986 A a s) (@lem5087987 A B g b s)). Qed.
Lemma lem5087989 {A B : Type'} (a : A) (g : B -> A) (b : B) (s : A -> Prop) : ((term1410 A s a) = (term1430 A B s g b)) = ((term1365 A a s) = (term1377 A B g b s)).
Proof. exact (TRANS (@lem5087983 A B a g b s) (@lem5087988 A B a g b s)). Qed.
Lemma lem5087990 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) (h2 : term586 A B t a s b y) : (term1365 A a s) = (term1377 A B g b s).
Proof. exact (EQ_MP (@lem5087989 A B a g b s) (@lem5087980 A B g t a s b y h1 h2)). Qed.
Lemma lem5087991 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term605 A B a t g s b y) (h3 : term586 A B t a s b y) : term1377 A B g b s.
Proof. exact (EQ_MP (@lem5087990 A B g t a s b y h2 h3) (@lem5087783 A a s h1)). Qed.
Lemma lem5088196 {B : Type'} (b : B) : (term1414 B b) = (term1414 B b).
Proof. exact (eq_refl (term1414 B b)). Qed.
Lemma lem5088197 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : (term1415 B b y) = (term1416 B b).
Proof. exact (MK_COMB (@lem5088196 B b) (@lem5085196 A B t a s b y h1)). Qed.
Lemma lem5088198 {B : Type'} (b : B) : (term1416 B b) = (term705 B b).
Proof. exact (eq_refl (term1416 B b)). Qed.
Lemma lem5088199 {B : Type'} (b : B) (y : B) : (term1417 B b y) = (term1417 B b y).
Proof. exact (eq_refl (term1417 B b y)). Qed.
Lemma lem5088200 {B : Type'} (y : B) (b : B) : ((term1415 B b y) = (term1416 B b)) = ((term1415 B b y) = (term705 B b)).
Proof. exact (MK_COMB (@lem5088199 B b y) (@lem5088198 B b)). Qed.
Lemma lem5088201 {B : Type'} (b : B) (y : B) : (term1415 B b y) = (term506 B b y).
Proof. exact (eq_refl (term1415 B b y)). Qed.
Lemma lem5088202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5088203 {B : Type'} (b : B) (y : B) : (term1417 B b y) = (term1418 B b y).
Proof. exact (MK_COMB (@lem5088202) (@lem5088201 B b y)). Qed.
Lemma lem5088204 {B : Type'} (b : B) : (term705 B b) = (term705 B b).
Proof. exact (eq_refl (term705 B b)). Qed.
Lemma lem5088205 {B : Type'} (y : B) (b : B) : ((term1415 B b y) = (term705 B b)) = ((term506 B b y) = (term705 B b)).
Proof. exact (MK_COMB (@lem5088203 B b y) (@lem5088204 B b)). Qed.
Lemma lem5088206 {B : Type'} (y : B) (b : B) : ((term1415 B b y) = (term1416 B b)) = ((term506 B b y) = (term705 B b)).
Proof. exact (TRANS (@lem5088200 B y b) (@lem5088205 B y b)). Qed.
Lemma lem5088207 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : (term506 B b y) = (term705 B b).
Proof. exact (EQ_MP (@lem5088206 B y b) (@lem5088197 A B t a s b y h1)). Qed.
Lemma lem5088417 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : term705 B b.
Proof. exact (EQ_MP (@lem5088207 A B t a s b y h2) (@lem5085200 B b y h1)). Qed.
Lemma lem5088498 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : a = (g y).
Proof. exact (SYM (@lem5085286 A B a t g s b y h1)). Qed.
Lemma lem5088568 {A : Type'} (s : A -> Prop) : (term1404 A s) = (term1404 A s).
Proof. exact (eq_refl (term1404 A s)). Qed.
Lemma lem5088569 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : (term1405 A s a) = (term1429 A B s g y).
Proof. exact (MK_COMB (@lem5088568 A s) (@lem5088498 A B a t g s b y h1)). Qed.
Lemma lem5088570 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term1429 A B s g y) = (term392 A B g y s).
Proof. exact (eq_refl (term1429 A B s g y)). Qed.
Lemma lem5088571 {A : Type'} (s : A -> Prop) (a : A) : (term1407 A s a) = (term1407 A s a).
Proof. exact (eq_refl (term1407 A s a)). Qed.
Lemma lem5088572 {A B : Type'} (a : A) (g : B -> A) (y : B) (s : A -> Prop) : ((term1405 A s a) = (term1429 A B s g y)) = ((term1405 A s a) = (term392 A B g y s)).
Proof. exact (MK_COMB (@lem5088571 A s a) (@lem5088570 A B g y s)). Qed.
Lemma lem5088573 {A : Type'} (a : A) (s : A -> Prop) : (term1405 A s a) = (@IN A a s).
Proof. exact (eq_refl (term1405 A s a)). Qed.
Lemma lem5088574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5088575 {A : Type'} (a : A) (s : A -> Prop) : (term1407 A s a) = (term1408 A a s).
Proof. exact (MK_COMB (@lem5088574) (@lem5088573 A a s)). Qed.
Lemma lem5088576 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term392 A B g y s) = (term392 A B g y s).
Proof. exact (eq_refl (term392 A B g y s)). Qed.
Lemma lem5088577 {A B : Type'} (a : A) (g : B -> A) (y : B) (s : A -> Prop) : ((term1405 A s a) = (term392 A B g y s)) = ((@IN A a s) = (term392 A B g y s)).
Proof. exact (MK_COMB (@lem5088575 A a s) (@lem5088576 A B g y s)). Qed.
Lemma lem5088578 {A B : Type'} (a : A) (g : B -> A) (y : B) (s : A -> Prop) : ((term1405 A s a) = (term1429 A B s g y)) = ((@IN A a s) = (term392 A B g y s)).
Proof. exact (TRANS (@lem5088572 A B a g y s) (@lem5088577 A B a g y s)). Qed.
Lemma lem5088579 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : (@IN A a s) = (term392 A B g y s).
Proof. exact (EQ_MP (@lem5088578 A B a g y s) (@lem5088569 A B a t g s b y h1)). Qed.
Lemma lem5088636 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term1377 A B g y s) : term1377 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5088717 {A B : Type'} (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : a = (g y).
Proof. exact (SYM (@lem5085378 A B a t g s b y h1)). Qed.
Lemma lem5088827 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : term506 B y b.
Proof. exact (proj1 (@lem5082082 A B t g s b y h1)). Qed.
Lemma lem5088884 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65377 : B) : (term1431 A B t b g _65377) = (term1431 A B t b g _65377).
Proof. exact (eq_refl (term1431 A B t b g _65377)). Qed.
Lemma lem5088885 {A B : Type'} (_65377 : B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : (term1432 A B t b g _65377 a) = (term1433 A B t b _65377 g y).
Proof. exact (MK_COMB (@lem5088884 A B t b g _65377) (@lem5088717 A B a t g s b y h1)). Qed.
Lemma lem5088886 {A B : Type'} (t : B -> Prop) (b : B) (_65377 : B) (g : B -> A) (y : B) : (term1433 A B t b _65377 g y) = (term1434 A B t b _65377 g y).
Proof. exact (eq_refl (term1433 A B t b _65377 g y)). Qed.
Lemma lem5088887 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65377 : B) (a : A) : (term1435 A B t b g _65377 a) = (term1435 A B t b g _65377 a).
Proof. exact (eq_refl (term1435 A B t b g _65377 a)). Qed.
Lemma lem5088888 {A B : Type'} (a : A) (t : B -> Prop) (b : B) (_65377 : B) (g : B -> A) (y : B) : ((term1432 A B t b g _65377 a) = (term1433 A B t b _65377 g y)) = ((term1432 A B t b g _65377 a) = (term1434 A B t b _65377 g y)).
Proof. exact (MK_COMB (@lem5088887 A B t b g _65377 a) (@lem5088886 A B t b _65377 g y)). Qed.
Lemma lem5088889 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65377 : B) (a : A) : (term1432 A B t b g _65377 a) = (term1397 A B t b g _65377 a).
Proof. exact (eq_refl (term1432 A B t b g _65377 a)). Qed.
Lemma lem5088890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5088891 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65377 : B) (a : A) : (term1435 A B t b g _65377 a) = (term1436 A B t b g _65377 a).
Proof. exact (MK_COMB (@lem5088890) (@lem5088889 A B t b g _65377 a)). Qed.
Lemma lem5088892 {A B : Type'} (t : B -> Prop) (b : B) (_65377 : B) (g : B -> A) (y : B) : (term1434 A B t b _65377 g y) = (term1434 A B t b _65377 g y).
Proof. exact (eq_refl (term1434 A B t b _65377 g y)). Qed.
Lemma lem5088893 {A B : Type'} (a : A) (t : B -> Prop) (b : B) (_65377 : B) (g : B -> A) (y : B) : ((term1432 A B t b g _65377 a) = (term1434 A B t b _65377 g y)) = ((term1397 A B t b g _65377 a) = (term1434 A B t b _65377 g y)).
Proof. exact (MK_COMB (@lem5088891 A B t b g _65377 a) (@lem5088892 A B t b _65377 g y)). Qed.
Lemma lem5088894 {A B : Type'} (a : A) (t : B -> Prop) (b : B) (_65377 : B) (g : B -> A) (y : B) : ((term1432 A B t b g _65377 a) = (term1433 A B t b _65377 g y)) = ((term1397 A B t b g _65377 a) = (term1434 A B t b _65377 g y)).
Proof. exact (TRANS (@lem5088888 A B a t b _65377 g y) (@lem5088893 A B a t b _65377 g y)). Qed.
Lemma lem5088895 {A B : Type'} (_65377 : B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term605 A B a t g s b y) : (term1397 A B t b g _65377 a) = (term1434 A B t b _65377 g y).
Proof. exact (EQ_MP (@lem5088894 A B a t b _65377 g y) (@lem5088885 A B _65377 a t g s b y h1)). Qed.
Lemma lem5088896 {A B : Type'} (_65377 : B) (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term1434 A B t b _65377 g y.
Proof. exact (EQ_MP (@lem5088895 A B _65377 a t g s b y h2) (@lem5085420 A B _65377 x a b t s f g y h1)). Qed.
Lemma lem5089073 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1365 A a s) : term1365 A a s.
Proof. exact (h1). Qed.
Lemma lem5089282 {B : Type'} (b : B) : (term1414 B b) = (term1414 B b).
Proof. exact (eq_refl (term1414 B b)). Qed.
Lemma lem5089283 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : (term1415 B b y) = (term1416 B b).
Proof. exact (MK_COMB (@lem5089282 B b) (@lem5085564 A B t a s b y h1)). Qed.
Lemma lem5089284 {B : Type'} (b : B) : (term1416 B b) = (term705 B b).
Proof. exact (eq_refl (term1416 B b)). Qed.
Lemma lem5089285 {B : Type'} (b : B) (y : B) : (term1417 B b y) = (term1417 B b y).
Proof. exact (eq_refl (term1417 B b y)). Qed.
Lemma lem5089286 {B : Type'} (y : B) (b : B) : ((term1415 B b y) = (term1416 B b)) = ((term1415 B b y) = (term705 B b)).
Proof. exact (MK_COMB (@lem5089285 B b y) (@lem5089284 B b)). Qed.
Lemma lem5089287 {B : Type'} (b : B) (y : B) : (term1415 B b y) = (term506 B b y).
Proof. exact (eq_refl (term1415 B b y)). Qed.
Lemma lem5089288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5089289 {B : Type'} (b : B) (y : B) : (term1417 B b y) = (term1418 B b y).
Proof. exact (MK_COMB (@lem5089288) (@lem5089287 B b y)). Qed.
Lemma lem5089290 {B : Type'} (b : B) : (term705 B b) = (term705 B b).
Proof. exact (eq_refl (term705 B b)). Qed.
Lemma lem5089291 {B : Type'} (y : B) (b : B) : ((term1415 B b y) = (term705 B b)) = ((term506 B b y) = (term705 B b)).
Proof. exact (MK_COMB (@lem5089289 B b y) (@lem5089290 B b)). Qed.
Lemma lem5089292 {B : Type'} (y : B) (b : B) : ((term1415 B b y) = (term1416 B b)) = ((term506 B b y) = (term705 B b)).
Proof. exact (TRANS (@lem5089286 B y b) (@lem5089291 B y b)). Qed.
Lemma lem5089293 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term586 A B t a s b y) : (term506 B b y) = (term705 B b).
Proof. exact (EQ_MP (@lem5089292 B y b) (@lem5089283 A B t a s b y h1)). Qed.
Lemma lem5089294 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : term705 B b.
Proof. exact (EQ_MP (@lem5089293 A B t a s b y h2) (@lem5085568 B b y h1)). Qed.
Lemma lem5089484 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term526 A B s b t a x) (h3 : term545 A B b s f t a x) : term434 A B f a t.
Proof. exact (EQ_MP (@lem5086227 A B b s f t a x h2 h3) (@lem5086006 A B x a b t s f g y h1)). Qed.
Lemma lem5089485 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term526 A B s b t a x) (h3 : term545 A B b s f t a x) : term1437 A B f a t.
Proof. exact (fun h0 : term1366 A B f a t => @lem5089484 A B g y b s f t a x h1 h2 h3). Qed.
Lemma lem5089487 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089488 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) : (term1437 A B f a t) = (term434 A B f a t).
Proof. exact (@lem5089487 (term434 A B f a t)). Qed.
Lemma lem5089489 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term526 A B s b t a x) (h3 : term545 A B b s f t a x) : term434 A B f a t.
Proof. exact (EQ_MP (@lem5089488 A B f a t) (@lem5089485 A B g y b s f t a x h1 h2 h3)). Qed.
Lemma lem5089492 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5089494 {A B : Type'} (f : A -> B) (a : A) (t : B -> Prop) : (term1366 A B f a t) = (term1439 A B f a t).
Proof. exact (@lem5089492 (term434 A B f a t)). Qed.
Lemma lem5089497 {A B : Type'} (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term526 A B s b t a x) (h3 : term545 A B b s f t a x) : term1439 A B f a t.
Proof. exact (EQ_MP (@lem5089494 A B f a t) (@lem5086255 A B b s f t a x h1 h2 h3)). Qed.
Lemma lem5089500 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : False.
Proof. exact (@lem5089497 A B b s f t a x h1 h3 h4 (@lem5089489 A B g y b s f t a x h2 h3 h4)). Qed.
Lemma lem5089501 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : term1440.
Proof. exact (fun h0 : ~ False => @lem5089500 A B g y b s f t a x h1 h2 h3 h4). Qed.
Lemma lem5089503 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089504 : term1440 = False.
Proof. exact (@lem5089503 False). Qed.
Lemma lem5089611 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5089612 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5089611 A x). Qed.
Lemma lem5089613 {A : Type'} (a : A) : a = a.
Proof. exact (@lem5089612 A a). Qed.
Lemma lem5089614 {A : Type'} (a : A) : term1441 A a.
Proof. exact (fun h0 : term705 A a => @lem5089613 A a). Qed.
Lemma lem5089616 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089617 {A : Type'} (a : A) : (term1441 A a) = (a = a).
Proof. exact (@lem5089616 (a = a)). Qed.
Lemma lem5089618 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem5089617 A a) (@lem5089614 A a)). Qed.
Lemma lem5089621 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5089623 {A : Type'} (a : A) : (term705 A a) = (term1442 A a).
Proof. exact (@lem5089621 (a = a)). Qed.
Lemma lem5089626 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : term1442 A a.
Proof. exact (EQ_MP (@lem5089623 A a) (@lem5086682 A B s b t a x h1 h2)). Qed.
Lemma lem5089629 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (@lem5089626 A B s b t a x h1 h2 (@lem5089618 A a)). Qed.
Lemma lem5089630 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : term1440.
Proof. exact (fun h0 : ~ False => @lem5089629 A B s b t a x h1 h2). Qed.
Lemma lem5089632 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089633 : term1440 = False.
Proof. exact (@lem5089632 False). Qed.
Lemma lem5089740 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term434 A B f x t.
Proof. exact (EQ_MP (@lem5086859 A B b s f t a x h2) (@lem5084548 A B x a b t s f g y h1)). Qed.
Lemma lem5089741 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term1437 A B f x t.
Proof. exact (fun h0 : term1366 A B f x t => @lem5089740 A B g y b s f t a x h1 h2). Qed.
Lemma lem5089743 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089744 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term1437 A B f x t) = (term434 A B f x t).
Proof. exact (@lem5089743 (term434 A B f x t)). Qed.
Lemma lem5089745 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term434 A B f x t.
Proof. exact (EQ_MP (@lem5089744 A B f x t) (@lem5089741 A B g y b s f t a x h1 h2)). Qed.
Lemma lem5089748 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5089750 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term1366 A B f x t) = (term1439 A B f x t).
Proof. exact (@lem5089748 (term434 A B f x t)). Qed.
Lemma lem5089753 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term1366 A B f x t) : term1439 A B f x t.
Proof. exact (EQ_MP (@lem5089750 A B f x t) (@lem5086902 A B f x t h1)). Qed.
Lemma lem5089756 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (@lem5089753 A B f x t h1 (@lem5089745 A B g y b s f t a x h2 h3)). Qed.
Lemma lem5089757 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : term1440.
Proof. exact (fun h0 : ~ False => @lem5089756 A B g y b s f t a x h1 h2 h3). Qed.
Lemma lem5089759 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089760 : term1440 = False.
Proof. exact (@lem5089759 False). Qed.
Lemma lem5089761 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5089760) (@lem5089757 A B g y b s f t a x h1 h2 h3)). Qed.
Lemma lem5089867 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : @IN A x s.
Proof. exact (proj1 (@lem5082055 A B s f t a x h1)). Qed.
Lemma lem5089868 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : term1443 A x s.
Proof. exact (fun h0 : term1365 A x s => @lem5089867 A B s f t a x h1). Qed.
Lemma lem5089870 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089871 {A : Type'} (x : A) (s : A -> Prop) : (term1443 A x s) = (@IN A x s).
Proof. exact (@lem5089870 (@IN A x s)). Qed.
Lemma lem5089872 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : @IN A x s.
Proof. exact (EQ_MP (@lem5089871 A x s) (@lem5089868 A B s f t a x h1)). Qed.
Lemma lem5089874 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5089875 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5089874 B x). Qed.
Lemma lem5089876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5089875 B (f x)). Qed.
Lemma lem5089877 {A B : Type'} (f : A -> B) (x : A) : term1444 A B f x.
Proof. exact (fun h0 : term1445 A B f x => @lem5089876 A B f x). Qed.
Lemma lem5089879 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5089880 {A B : Type'} (f : A -> B) (x : A) : (term1444 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5089879 ((f x) = (f x))). Qed.
Lemma lem5089881 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5089880 A B f x) (@lem5089877 A B f x)). Qed.
Lemma lem5089887 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5089888 {A B : Type'} (a : A) (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : (term1422 A B s a _65360 f x) = (term1446 A B a s _65360 f x).
Proof. exact (@lem5089887 (_65360 = a) (term1365 A _65360 s) (term1447 A B _65360 f x)). Qed.
Lemma lem5089904 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5089905 {A B : Type'} (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : (term1448 A B s _65360 f x) = (term1449 A B f x _65360 s).
Proof. exact (@lem5089904 (term1447 A B _65360 f x) (term1365 A _65360 s)). Qed.
Lemma lem5089913 {A : Type'} (_65360 : A) (a : A) : (term413 A _65360 a) = (term413 A _65360 a).
Proof. exact (eq_refl (term413 A _65360 a)). Qed.
Lemma lem5089914 {A B : Type'} (a : A) (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : (term1446 A B a s _65360 f x) = (term1450 A B a f x _65360 s).
Proof. exact (MK_COMB (@lem5089913 A _65360 a) (@lem5089905 A B f x _65360 s)). Qed.
Lemma lem5089925 {A B : Type'} (a : A) (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : (term1422 A B s a _65360 f x) = (term1450 A B a f x _65360 s).
Proof. exact (TRANS (@lem5089888 A B a s _65360 f x) (@lem5089914 A B a f x _65360 s)). Qed.
Lemma lem5089926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5089927 {A B : Type'} (a : A) (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : (term1451 A B s a _65360 f x) = (term1452 A B a f x _65360 s).
Proof. exact (MK_COMB (@lem5089926) (@lem5089925 A B a f x _65360 s)). Qed.
Lemma lem5089943 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5089944 {A B : Type'} (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : (term1448 A B s _65360 f x) = (term1449 A B f x _65360 s).
Proof. exact (@lem5089943 (term1447 A B _65360 f x) (term1365 A _65360 s)). Qed.
Lemma lem5089952 {A : Type'} (_65360 : A) (a : A) : (term413 A _65360 a) = (term413 A _65360 a).
Proof. exact (eq_refl (term413 A _65360 a)). Qed.
Lemma lem5089953 {A B : Type'} (a : A) (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : (term1446 A B a s _65360 f x) = (term1450 A B a f x _65360 s).
Proof. exact (MK_COMB (@lem5089952 A _65360 a) (@lem5089944 A B f x _65360 s)). Qed.
Lemma lem5089964 {A B : Type'} (a : A) (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : ((term1422 A B s a _65360 f x) = (term1446 A B a s _65360 f x)) = ((term1450 A B a f x _65360 s) = (term1450 A B a f x _65360 s)).
Proof. exact (MK_COMB (@lem5089927 A B a f x _65360 s) (@lem5089953 A B a f x _65360 s)). Qed.
Lemma lem5089966 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5089967 (x : Prop) : (x = x) = True.
Proof. exact (@lem5089966 Prop x). Qed.
Lemma lem5089968 {A B : Type'} (a : A) (f : A -> B) (x : A) (_65360 : A) (s : A -> Prop) : ((term1450 A B a f x _65360 s) = (term1450 A B a f x _65360 s)) = True.
Proof. exact (@lem5089967 (term1450 A B a f x _65360 s)). Qed.
Lemma lem5089969 {A B : Type'} (a : A) (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : ((term1422 A B s a _65360 f x) = (term1446 A B a s _65360 f x)) = True.
Proof. exact (TRANS (@lem5089964 A B a f x _65360 s) (@lem5089968 A B a f x _65360 s)). Qed.
Lemma lem5089970 {A B : Type'} (a : A) (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : True = ((term1422 A B s a _65360 f x) = (term1446 A B a s _65360 f x)).
Proof. exact (SYM (@lem5089969 A B a s _65360 f x)). Qed.
Lemma lem5089971 {A B : Type'} (a : A) (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : (term1422 A B s a _65360 f x) = (term1446 A B a s _65360 f x).
Proof. exact (EQ_MP (@lem5089970 A B a s _65360 f x) (@lem0)). Qed.
Lemma lem5089972 {A B : Type'} (_65360 : A) (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term1446 A B a s _65360 f x.
Proof. exact (EQ_MP (@lem5089971 A B a s _65360 f x) (@lem5087202 A B _65360 g y b s f t a x h1 h2)). Qed.
Lemma lem5089974 (b : Prop) (a : Prop) : (a \/ b) = (term1453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5089975 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (_65360 : A) (a : A) : (term1446 A B a s _65360 f x) = (term1454 A B s f x _65360 a).
Proof. exact (@lem5089974 (term1448 A B s _65360 f x) (_65360 = a)). Qed.
Lemma lem5089977 (a : Prop) (b : Prop) : (term1455 a b) = (term1456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5089978 {A B : Type'} (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : (term1457 A B s _65360 f x) = (term1458 A B s _65360 f x).
Proof. exact (@lem5089977 (term1365 A _65360 s) (term1447 A B _65360 f x)). Qed.
Lemma lem5089980 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5089981 {A : Type'} (_65360 : A) (s : A -> Prop) : (term1459 A _65360 s) = (@IN A _65360 s).
Proof. exact (@lem5089980 (@IN A _65360 s)). Qed.
Lemma lem5089982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5089983 {A : Type'} (_65360 : A) (s : A -> Prop) : (term1460 A _65360 s) = (term402 A _65360 s).
Proof. exact (MK_COMB (@lem5089982) (@lem5089981 A _65360 s)). Qed.
Lemma lem5089985 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5089986 {A B : Type'} (_65360 : A) (f : A -> B) (x : A) : (term1461 A B _65360 f x) = ((f _65360) = (f x)).
Proof. exact (@lem5089985 ((f _65360) = (f x))). Qed.
Lemma lem5089987 {A B : Type'} (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : (term1458 A B s _65360 f x) = (term1462 A B s _65360 f x).
Proof. exact (MK_COMB (@lem5089983 A _65360 s) (@lem5089986 A B _65360 f x)). Qed.
Lemma lem5089988 {A B : Type'} (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : (term1457 A B s _65360 f x) = (term1462 A B s _65360 f x).
Proof. exact (TRANS (@lem5089978 A B s _65360 f x) (@lem5089987 A B s _65360 f x)). Qed.
Lemma lem5089989 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5089990 {A B : Type'} (s : A -> Prop) (_65360 : A) (f : A -> B) (x : A) : (term1463 A B s _65360 f x) = (term1464 A B s _65360 f x).
Proof. exact (MK_COMB (@lem5089989) (@lem5089988 A B s _65360 f x)). Qed.
Lemma lem5089991 {A : Type'} (_65360 : A) (a : A) : (_65360 = a) = (_65360 = a).
Proof. exact (eq_refl (_65360 = a)). Qed.
Lemma lem5089992 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (_65360 : A) (a : A) : (term1454 A B s f x _65360 a) = (term1465 A B s f x _65360 a).
Proof. exact (MK_COMB (@lem5089990 A B s _65360 f x) (@lem5089991 A _65360 a)). Qed.
Lemma lem5089993 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (_65360 : A) (a : A) : (term1446 A B a s _65360 f x) = (term1465 A B s f x _65360 a).
Proof. exact (TRANS (@lem5089975 A B s f x _65360 a) (@lem5089992 A B s f x _65360 a)). Qed.
Lemma lem5089995 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : term1466 A B s f x.
Proof. exact (conj (@lem5089872 A B s f t a x h1) (@lem5089881 A B f x)). Qed.
Lemma lem5089997 {A B : Type'} (_65360 : A) (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term1465 A B s f x _65360 a.
Proof. exact (EQ_MP (@lem5089993 A B s f x _65360 a) (@lem5089972 A B _65360 g y b s f t a x h1 h2)). Qed.
Lemma lem5089998 {A B : Type'} (_65360 : A) (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term1465 A B s f x _65360 a.
Proof. exact (@lem5089997 A B _65360 g y b s f t a x h1 h2). Qed.
Lemma lem5089999 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : term1467 A B s f x a.
Proof. exact (@lem5089998 A B x g y b s f t a x h1 h2). Qed.
Lemma lem5090002 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : x = a.
Proof. exact (@lem5089999 A B g y b s f t a x h2 h3 (@lem5089995 A B s f t a x h1)). Qed.
Lemma lem5090003 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : term1468 A x a.
Proof. exact (fun h0 : term506 A x a => @lem5090002 A B g y b s f t a x h1 h2 h3). Qed.
Lemma lem5090005 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090006 {A : Type'} (x : A) (a : A) : (term1468 A x a) = (x = a).
Proof. exact (@lem5090005 (x = a)). Qed.
Lemma lem5090007 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : x = a.
Proof. exact (EQ_MP (@lem5090006 A x a) (@lem5090003 A B g y b s f t a x h1 h2 h3)). Qed.
Lemma lem5090010 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5090012 {A : Type'} (x : A) (a : A) : (term506 A x a) = (term1469 A x a).
Proof. exact (@lem5090010 (x = a)). Qed.
Lemma lem5090015 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) : term1469 A x a.
Proof. exact (EQ_MP (@lem5090012 A x a) (@lem5087094 A B s f t a x h1)). Qed.
Lemma lem5090018 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (@lem5090015 A B s f t a x h1 (@lem5090007 A B g y b s f t a x h1 h2 h3)). Qed.
Lemma lem5090019 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : term1440.
Proof. exact (fun h0 : ~ False => @lem5090018 A B g y b s f t a x h1 h2 h3). Qed.
Lemma lem5090021 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090022 : term1440 = False.
Proof. exact (@lem5090021 False). Qed.
Lemma lem5090129 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN B b t.
Proof. exact (proj1 (@lem5082033 A B x a b t s f g y h1)). Qed.
Lemma lem5090130 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1443 B b t.
Proof. exact (fun h0 : term1365 B b t => @lem5090129 A B x a b t s f g y h1). Qed.
Lemma lem5090132 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090133 {B : Type'} (b : B) (t : B -> Prop) : (term1443 B b t) = (@IN B b t).
Proof. exact (@lem5090132 (@IN B b t)). Qed.
Lemma lem5090134 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN B b t.
Proof. exact (EQ_MP (@lem5090133 B b t) (@lem5090130 A B x a b t s f g y h1)). Qed.
Lemma lem5090137 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5090139 {B : Type'} (b : B) (t : B -> Prop) : (term1365 B b t) = (term1470 B b t).
Proof. exact (@lem5090137 (@IN B b t)). Qed.
Lemma lem5090142 {B : Type'} (b : B) (t : B -> Prop) (h1 : term1365 B b t) : term1470 B b t.
Proof. exact (EQ_MP (@lem5090139 B b t) (@lem5087340 B b t h1)). Qed.
Lemma lem5090145 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (@lem5090142 B b t h1 (@lem5090134 A B x a b t s f g y h2)). Qed.
Lemma lem5090146 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5090145 A B x a b t s f g y h1 h2). Qed.
Lemma lem5090148 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090149 : term1440 = False.
Proof. exact (@lem5090148 False). Qed.
Lemma lem5090150 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5090149) (@lem5090146 A B x a b t s f g y h1 h2)). Qed.
Lemma lem5090256 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5090257 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5090256 A x). Qed.
Lemma lem5090258 {A : Type'} (a : A) : a = a.
Proof. exact (@lem5090257 A a). Qed.
Lemma lem5090259 {A : Type'} (a : A) : term1441 A a.
Proof. exact (fun h0 : term705 A a => @lem5090258 A a). Qed.
Lemma lem5090261 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090262 {A : Type'} (a : A) : (term1441 A a) = (a = a).
Proof. exact (@lem5090261 (a = a)). Qed.
Lemma lem5090263 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem5090262 A a) (@lem5090259 A a)). Qed.
Lemma lem5090266 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5090268 {A : Type'} (a : A) : (term705 A a) = (term1442 A a).
Proof. exact (@lem5090266 (a = a)). Qed.
Lemma lem5090271 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : term1442 A a.
Proof. exact (EQ_MP (@lem5090268 A a) (@lem5087561 A B s b t a x h1 h2)). Qed.
Lemma lem5090274 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (@lem5090271 A B s b t a x h1 h2 (@lem5090263 A a)). Qed.
Lemma lem5090275 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : term1440.
Proof. exact (fun h0 : ~ False => @lem5090274 A B s b t a x h1 h2). Qed.
Lemma lem5090277 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090278 : term1440 = False.
Proof. exact (@lem5090277 False). Qed.
Lemma lem5090385 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5082071 A B a s t g f x h1)). Qed.
Lemma lem5090386 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term1443 A x s.
Proof. exact (fun h0 : term1365 A x s => @lem5090385 A B a s t g f x h1). Qed.
Lemma lem5090388 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090389 {A : Type'} (x : A) (s : A -> Prop) : (term1443 A x s) = (@IN A x s).
Proof. exact (@lem5090388 (@IN A x s)). Qed.
Lemma lem5090390 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5090389 A x s) (@lem5090386 A B a s t g f x h1)). Qed.
Lemma lem5090392 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term506 A x a.
Proof. exact (proj1 (@lem5082064 A B a s t g f x h1)). Qed.
Lemma lem5090393 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term1471 A x a.
Proof. exact (fun h0 : x = a => @lem5090392 A B a s t g f x h1). Qed.
Lemma lem5090395 (p : Prop) : (term1472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5090396 {A : Type'} (x : A) (a : A) : (term1471 A x a) = (term506 A x a).
Proof. exact (@lem5090395 (x = a)). Qed.
Lemma lem5090397 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term506 A x a.
Proof. exact (EQ_MP (@lem5090396 A x a) (@lem5090393 A B a s t g f x h1)). Qed.
Lemma lem5090403 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5090404 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (_65366 : A) (t : B -> Prop) : (term1395 A B s a f _65366 t) = (term1473 A B a s f _65366 t).
Proof. exact (@lem5090403 (_65366 = a) (term1365 A _65366 s) (term434 A B f _65366 t)). Qed.
Lemma lem5090420 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5090421 {A B : Type'} (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : (term1474 A B s f _65366 t) = (term1475 A B f t _65366 s).
Proof. exact (@lem5090420 (term434 A B f _65366 t) (term1365 A _65366 s)). Qed.
Lemma lem5090427 {A : Type'} (_65366 : A) (a : A) : (term413 A _65366 a) = (term413 A _65366 a).
Proof. exact (eq_refl (term413 A _65366 a)). Qed.
Lemma lem5090428 {A B : Type'} (a : A) (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : (term1473 A B a s f _65366 t) = (term1476 A B a f t _65366 s).
Proof. exact (MK_COMB (@lem5090427 A _65366 a) (@lem5090421 A B f t _65366 s)). Qed.
Lemma lem5090439 {A B : Type'} (a : A) (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : (term1395 A B s a f _65366 t) = (term1476 A B a f t _65366 s).
Proof. exact (TRANS (@lem5090404 A B a s f _65366 t) (@lem5090428 A B a f t _65366 s)). Qed.
Lemma lem5090440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5090441 {A B : Type'} (a : A) (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : (term1477 A B s a f _65366 t) = (term1478 A B a f t _65366 s).
Proof. exact (MK_COMB (@lem5090440) (@lem5090439 A B a f t _65366 s)). Qed.
Lemma lem5090455 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5090456 {A : Type'} (a : A) (_65366 : A) (s : A -> Prop) : (term504 A s _65366 a) = (term1479 A a _65366 s).
Proof. exact (@lem5090455 (_65366 = a) (term1365 A _65366 s)). Qed.
Lemma lem5090464 {A B : Type'} (f : A -> B) (_65366 : A) (t : B -> Prop) : (term1480 A B f _65366 t) = (term1480 A B f _65366 t).
Proof. exact (eq_refl (term1480 A B f _65366 t)). Qed.
Lemma lem5090465 {A B : Type'} (f : A -> B) (t : B -> Prop) (a : A) (_65366 : A) (s : A -> Prop) : (term1481 A B f t s _65366 a) = (term1482 A B f t a _65366 s).
Proof. exact (MK_COMB (@lem5090464 A B f _65366 t) (@lem5090456 A a _65366 s)). Qed.
Lemma lem5090469 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5090470 {A B : Type'} (a : A) (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : (term1482 A B f t a _65366 s) = (term1476 A B a f t _65366 s).
Proof. exact (@lem5090469 (_65366 = a) (term434 A B f _65366 t) (term1365 A _65366 s)). Qed.
Lemma lem5090488 {A B : Type'} (a : A) (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : (term1481 A B f t s _65366 a) = (term1476 A B a f t _65366 s).
Proof. exact (TRANS (@lem5090465 A B f t a _65366 s) (@lem5090470 A B a f t _65366 s)). Qed.
Lemma lem5090489 {A B : Type'} (a : A) (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : ((term1395 A B s a f _65366 t) = (term1481 A B f t s _65366 a)) = ((term1476 A B a f t _65366 s) = (term1476 A B a f t _65366 s)).
Proof. exact (MK_COMB (@lem5090441 A B a f t _65366 s) (@lem5090488 A B a f t _65366 s)). Qed.
Lemma lem5090491 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5090492 (x : Prop) : (x = x) = True.
Proof. exact (@lem5090491 Prop x). Qed.
Lemma lem5090493 {A B : Type'} (a : A) (f : A -> B) (t : B -> Prop) (_65366 : A) (s : A -> Prop) : ((term1476 A B a f t _65366 s) = (term1476 A B a f t _65366 s)) = True.
Proof. exact (@lem5090492 (term1476 A B a f t _65366 s)). Qed.
Lemma lem5090494 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (_65366 : A) (a : A) : ((term1395 A B s a f _65366 t) = (term1481 A B f t s _65366 a)) = True.
Proof. exact (TRANS (@lem5090489 A B a f t _65366 s) (@lem5090493 A B a f t _65366 s)). Qed.
Lemma lem5090495 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (_65366 : A) (a : A) : True = ((term1395 A B s a f _65366 t) = (term1481 A B f t s _65366 a)).
Proof. exact (SYM (@lem5090494 A B f t s _65366 a)). Qed.
Lemma lem5090496 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (_65366 : A) (a : A) : (term1395 A B s a f _65366 t) = (term1481 A B f t s _65366 a).
Proof. exact (EQ_MP (@lem5090495 A B f t s _65366 a) (@lem0)). Qed.
Lemma lem5090497 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1481 A B f t s _65366 a.
Proof. exact (EQ_MP (@lem5090496 A B f t s _65366 a) (@lem5084984 A B _65366 x a b t s f g y h1)). Qed.
Lemma lem5090499 (b : Prop) (a : Prop) : (a \/ b) = (term1453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5090500 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65366 : A) (t : B -> Prop) : (term1481 A B f t s _65366 a) = (term1483 A B s a f _65366 t).
Proof. exact (@lem5090499 (term504 A s _65366 a) (term434 A B f _65366 t)). Qed.
Lemma lem5090502 (a : Prop) (b : Prop) : (term1455 a b) = (term1456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5090503 {A : Type'} (s : A -> Prop) (_65366 : A) (a : A) : (term1484 A s _65366 a) = (term1485 A s _65366 a).
Proof. exact (@lem5090502 (term1365 A _65366 s) (_65366 = a)). Qed.
Lemma lem5090505 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5090506 {A : Type'} (_65366 : A) (s : A -> Prop) : (term1459 A _65366 s) = (@IN A _65366 s).
Proof. exact (@lem5090505 (@IN A _65366 s)). Qed.
Lemma lem5090507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5090508 {A : Type'} (_65366 : A) (s : A -> Prop) : (term1460 A _65366 s) = (term402 A _65366 s).
Proof. exact (MK_COMB (@lem5090507) (@lem5090506 A _65366 s)). Qed.
Lemma lem5090509 {A : Type'} (_65366 : A) (a : A) : (term506 A _65366 a) = (term506 A _65366 a).
Proof. exact (eq_refl (term506 A _65366 a)). Qed.
Lemma lem5090510 {A : Type'} (s : A -> Prop) (_65366 : A) (a : A) : (term1485 A s _65366 a) = (term27 A s _65366 a).
Proof. exact (MK_COMB (@lem5090508 A _65366 s) (@lem5090509 A _65366 a)). Qed.
Lemma lem5090511 {A : Type'} (s : A -> Prop) (_65366 : A) (a : A) : (term1484 A s _65366 a) = (term27 A s _65366 a).
Proof. exact (TRANS (@lem5090503 A s _65366 a) (@lem5090510 A s _65366 a)). Qed.
Lemma lem5090512 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5090513 {A : Type'} (s : A -> Prop) (_65366 : A) (a : A) : (term1486 A s _65366 a) = (term1487 A s _65366 a).
Proof. exact (MK_COMB (@lem5090512) (@lem5090511 A s _65366 a)). Qed.
Lemma lem5090514 {A B : Type'} (f : A -> B) (_65366 : A) (t : B -> Prop) : (term434 A B f _65366 t) = (term434 A B f _65366 t).
Proof. exact (eq_refl (term434 A B f _65366 t)). Qed.
Lemma lem5090515 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65366 : A) (t : B -> Prop) : (term1483 A B s a f _65366 t) = (term1488 A B s a f _65366 t).
Proof. exact (MK_COMB (@lem5090513 A s _65366 a) (@lem5090514 A B f _65366 t)). Qed.
Lemma lem5090516 {A B : Type'} (s : A -> Prop) (a : A) (f : A -> B) (_65366 : A) (t : B -> Prop) : (term1481 A B f t s _65366 a) = (term1488 A B s a f _65366 t).
Proof. exact (TRANS (@lem5090500 A B s a f _65366 t) (@lem5090515 A B s a f _65366 t)). Qed.
Lemma lem5090518 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term27 A s x a.
Proof. exact (conj (@lem5090390 A B a s t g f x h1) (@lem5090397 A B a s t g f x h1)). Qed.
Lemma lem5090520 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1488 A B s a f _65366 t.
Proof. exact (EQ_MP (@lem5090516 A B s a f _65366 t) (@lem5090497 A B _65366 x a b t s f g y h1)). Qed.
Lemma lem5090521 {A B : Type'} (_65366 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1488 A B s a f _65366 t.
Proof. exact (@lem5090520 A B _65366 x a b t s f g y h1). Qed.
Lemma lem5090522 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1488 A B s a f x t.
Proof. exact (@lem5090521 A B x x a b t s f g y h1). Qed.
Lemma lem5090525 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term554 A B a s t g f x) (h2 : term1177 A B x a b t s f g y) : term434 A B f x t.
Proof. exact (@lem5090522 A B x a b t s f g y h2 (@lem5090518 A B a s t g f x h1)). Qed.
Lemma lem5090526 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term554 A B a s t g f x) (h2 : term1177 A B x a b t s f g y) : term1437 A B f x t.
Proof. exact (fun h0 : term1366 A B f x t => @lem5090525 A B x a b t s f g y h1 h2). Qed.
Lemma lem5090528 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090529 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term1437 A B f x t) = (term434 A B f x t).
Proof. exact (@lem5090528 (term434 A B f x t)). Qed.
Lemma lem5090530 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term554 A B a s t g f x) (h2 : term1177 A B x a b t s f g y) : term434 A B f x t.
Proof. exact (EQ_MP (@lem5090529 A B f x t) (@lem5090526 A B x a b t s f g y h1 h2)). Qed.
Lemma lem5090533 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5090535 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term1366 A B f x t) = (term1439 A B f x t).
Proof. exact (@lem5090533 (term434 A B f x t)). Qed.
Lemma lem5090538 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term1366 A B f x t) : term1439 A B f x t.
Proof. exact (EQ_MP (@lem5090535 A B f x t) (@lem5084924 A B f x t h1)). Qed.
Lemma lem5090541 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (@lem5090538 A B f x t h1 (@lem5090530 A B x a b t s f g y h2 h3)). Qed.
Lemma lem5090542 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5090541 A B x a b t s f g y h1 h2 h3). Qed.
Lemma lem5090544 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090545 : term1440 = False.
Proof. exact (@lem5090544 False). Qed.
Lemma lem5090546 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5090545) (@lem5090542 A B x a b t s f g y h1 h2 h3)). Qed.
Lemma lem5090652 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5082071 A B a s t g f x h1)). Qed.
Lemma lem5090653 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term1443 A x s.
Proof. exact (fun h0 : term1365 A x s => @lem5090652 A B a s t g f x h1). Qed.
Lemma lem5090655 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090656 {A : Type'} (x : A) (s : A -> Prop) : (term1443 A x s) = (@IN A x s).
Proof. exact (@lem5090655 (@IN A x s)). Qed.
Lemma lem5090657 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5090656 A x s) (@lem5090653 A B a s t g f x h1)). Qed.
Lemma lem5090659 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term506 A x a.
Proof. exact (proj1 (@lem5082064 A B a s t g f x h1)). Qed.
Lemma lem5090660 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term1471 A x a.
Proof. exact (fun h0 : x = a => @lem5090659 A B a s t g f x h1). Qed.
Lemma lem5090662 (p : Prop) : (term1472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5090663 {A : Type'} (x : A) (a : A) : (term1471 A x a) = (term506 A x a).
Proof. exact (@lem5090662 (x = a)). Qed.
Lemma lem5090664 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term506 A x a.
Proof. exact (EQ_MP (@lem5090663 A x a) (@lem5090660 A B a s t g f x h1)). Qed.
Lemma lem5090670 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5090671 {A B : Type'} (a : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (_65368 : A) : (term1396 A B s a g f _65368) = (term1489 A B a s g f _65368).
Proof. exact (@lem5090670 (_65368 = a) (term1365 A _65368 s) ((term100 A B g f _65368) = _65368)). Qed.
Lemma lem5090687 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5090688 {A B : Type'} (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : (term1490 A B s g f _65368) = (term1491 A B g f _65368 s).
Proof. exact (@lem5090687 ((term100 A B g f _65368) = _65368) (term1365 A _65368 s)). Qed.
Lemma lem5090696 {A : Type'} (_65368 : A) (a : A) : (term413 A _65368 a) = (term413 A _65368 a).
Proof. exact (eq_refl (term413 A _65368 a)). Qed.
Lemma lem5090697 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : (term1489 A B a s g f _65368) = (term1492 A B a g f _65368 s).
Proof. exact (MK_COMB (@lem5090696 A _65368 a) (@lem5090688 A B g f _65368 s)). Qed.
Lemma lem5090708 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : (term1396 A B s a g f _65368) = (term1492 A B a g f _65368 s).
Proof. exact (TRANS (@lem5090671 A B a s g f _65368) (@lem5090697 A B a g f _65368 s)). Qed.
Lemma lem5090709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5090710 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : (term1493 A B s a g f _65368) = (term1494 A B a g f _65368 s).
Proof. exact (MK_COMB (@lem5090709) (@lem5090708 A B a g f _65368 s)). Qed.
Lemma lem5090726 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5090727 {A : Type'} (a : A) (_65368 : A) (s : A -> Prop) : (term504 A s _65368 a) = (term1479 A a _65368 s).
Proof. exact (@lem5090726 (_65368 = a) (term1365 A _65368 s)). Qed.
Lemma lem5090735 {A B : Type'} (g : B -> A) (f : A -> B) (_65368 : A) : (term1495 A B g f _65368) = (term1495 A B g f _65368).
Proof. exact (eq_refl (term1495 A B g f _65368)). Qed.
Lemma lem5090736 {A B : Type'} (g : B -> A) (f : A -> B) (a : A) (_65368 : A) (s : A -> Prop) : (term1496 A B g f s _65368 a) = (term1497 A B g f a _65368 s).
Proof. exact (MK_COMB (@lem5090735 A B g f _65368) (@lem5090727 A a _65368 s)). Qed.
Lemma lem5090740 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5090741 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : (term1497 A B g f a _65368 s) = (term1492 A B a g f _65368 s).
Proof. exact (@lem5090740 (_65368 = a) ((term100 A B g f _65368) = _65368) (term1365 A _65368 s)). Qed.
Lemma lem5090761 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : (term1496 A B g f s _65368 a) = (term1492 A B a g f _65368 s).
Proof. exact (TRANS (@lem5090736 A B g f a _65368 s) (@lem5090741 A B a g f _65368 s)). Qed.
Lemma lem5090762 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : ((term1396 A B s a g f _65368) = (term1496 A B g f s _65368 a)) = ((term1492 A B a g f _65368 s) = (term1492 A B a g f _65368 s)).
Proof. exact (MK_COMB (@lem5090710 A B a g f _65368 s) (@lem5090761 A B a g f _65368 s)). Qed.
Lemma lem5090764 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5090765 (x : Prop) : (x = x) = True.
Proof. exact (@lem5090764 Prop x). Qed.
Lemma lem5090766 {A B : Type'} (a : A) (g : B -> A) (f : A -> B) (_65368 : A) (s : A -> Prop) : ((term1492 A B a g f _65368 s) = (term1492 A B a g f _65368 s)) = True.
Proof. exact (@lem5090765 (term1492 A B a g f _65368 s)). Qed.
Lemma lem5090767 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_65368 : A) (a : A) : ((term1396 A B s a g f _65368) = (term1496 A B g f s _65368 a)) = True.
Proof. exact (TRANS (@lem5090762 A B a g f _65368 s) (@lem5090766 A B a g f _65368 s)). Qed.
Lemma lem5090768 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_65368 : A) (a : A) : True = ((term1396 A B s a g f _65368) = (term1496 A B g f s _65368 a)).
Proof. exact (SYM (@lem5090767 A B g f s _65368 a)). Qed.
Lemma lem5090769 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_65368 : A) (a : A) : (term1396 A B s a g f _65368) = (term1496 A B g f s _65368 a).
Proof. exact (EQ_MP (@lem5090768 A B g f s _65368 a) (@lem0)). Qed.
Lemma lem5090770 {A B : Type'} (_65368 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1496 A B g f s _65368 a.
Proof. exact (EQ_MP (@lem5090769 A B g f s _65368 a) (@lem5085064 A B _65368 x a b t s f g y h1)). Qed.
Lemma lem5090772 (b : Prop) (a : Prop) : (a \/ b) = (term1453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5090773 {A B : Type'} (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (_65368 : A) : (term1496 A B g f s _65368 a) = (term1498 A B s a g f _65368).
Proof. exact (@lem5090772 (term504 A s _65368 a) ((term100 A B g f _65368) = _65368)). Qed.
Lemma lem5090775 (a : Prop) (b : Prop) : (term1455 a b) = (term1456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5090776 {A : Type'} (s : A -> Prop) (_65368 : A) (a : A) : (term1484 A s _65368 a) = (term1485 A s _65368 a).
Proof. exact (@lem5090775 (term1365 A _65368 s) (_65368 = a)). Qed.
Lemma lem5090778 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5090779 {A : Type'} (_65368 : A) (s : A -> Prop) : (term1459 A _65368 s) = (@IN A _65368 s).
Proof. exact (@lem5090778 (@IN A _65368 s)). Qed.
Lemma lem5090780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5090781 {A : Type'} (_65368 : A) (s : A -> Prop) : (term1460 A _65368 s) = (term402 A _65368 s).
Proof. exact (MK_COMB (@lem5090780) (@lem5090779 A _65368 s)). Qed.
Lemma lem5090782 {A : Type'} (_65368 : A) (a : A) : (term506 A _65368 a) = (term506 A _65368 a).
Proof. exact (eq_refl (term506 A _65368 a)). Qed.
Lemma lem5090783 {A : Type'} (s : A -> Prop) (_65368 : A) (a : A) : (term1485 A s _65368 a) = (term27 A s _65368 a).
Proof. exact (MK_COMB (@lem5090781 A _65368 s) (@lem5090782 A _65368 a)). Qed.
Lemma lem5090784 {A : Type'} (s : A -> Prop) (_65368 : A) (a : A) : (term1484 A s _65368 a) = (term27 A s _65368 a).
Proof. exact (TRANS (@lem5090776 A s _65368 a) (@lem5090783 A s _65368 a)). Qed.
Lemma lem5090785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5090786 {A : Type'} (s : A -> Prop) (_65368 : A) (a : A) : (term1486 A s _65368 a) = (term1487 A s _65368 a).
Proof. exact (MK_COMB (@lem5090785) (@lem5090784 A s _65368 a)). Qed.
Lemma lem5090787 {A B : Type'} (g : B -> A) (f : A -> B) (_65368 : A) : ((term100 A B g f _65368) = _65368) = ((term100 A B g f _65368) = _65368).
Proof. exact (eq_refl ((term100 A B g f _65368) = _65368)). Qed.
Lemma lem5090788 {A B : Type'} (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (_65368 : A) : (term1498 A B s a g f _65368) = (term1499 A B s a g f _65368).
Proof. exact (MK_COMB (@lem5090786 A s _65368 a) (@lem5090787 A B g f _65368)). Qed.
Lemma lem5090789 {A B : Type'} (s : A -> Prop) (a : A) (g : B -> A) (f : A -> B) (_65368 : A) : (term1496 A B g f s _65368 a) = (term1499 A B s a g f _65368).
Proof. exact (TRANS (@lem5090773 A B s a g f _65368) (@lem5090788 A B s a g f _65368)). Qed.
Lemma lem5090791 {A B : Type'} (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term554 A B a s t g f x) : term27 A s x a.
Proof. exact (conj (@lem5090657 A B a s t g f x h1) (@lem5090664 A B a s t g f x h1)). Qed.
Lemma lem5090793 {A B : Type'} (_65368 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1499 A B s a g f _65368.
Proof. exact (EQ_MP (@lem5090789 A B s a g f _65368) (@lem5090770 A B _65368 x a b t s f g y h1)). Qed.
Lemma lem5090794 {A B : Type'} (_65368 : A) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1499 A B s a g f _65368.
Proof. exact (@lem5090793 A B _65368 x a b t s f g y h1). Qed.
Lemma lem5090795 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1499 A B s a g f x.
Proof. exact (@lem5090794 A B x x a b t s f g y h1). Qed.
Lemma lem5090798 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term554 A B a s t g f x) (h2 : term1177 A B x a b t s f g y) : (term100 A B g f x) = x.
Proof. exact (@lem5090795 A B x a b t s f g y h2 (@lem5090791 A B a s t g f x h1)). Qed.
Lemma lem5090799 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term554 A B a s t g f x) (h2 : term1177 A B x a b t s f g y) : term1500 A B g f x.
Proof. exact (fun h0 : term1376 A B g f x => @lem5090798 A B x a b t s f g y h1 h2). Qed.
Lemma lem5090801 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090802 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term1500 A B g f x) = ((term100 A B g f x) = x).
Proof. exact (@lem5090801 ((term100 A B g f x) = x)). Qed.
Lemma lem5090803 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term554 A B a s t g f x) (h2 : term1177 A B x a b t s f g y) : (term100 A B g f x) = x.
Proof. exact (EQ_MP (@lem5090802 A B g f x) (@lem5090799 A B x a b t s f g y h1 h2)). Qed.
Lemma lem5090806 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5090808 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term1376 A B g f x) = (term1501 A B g f x).
Proof. exact (@lem5090806 ((term100 A B g f x) = x)). Qed.
Lemma lem5090811 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term1376 A B g f x) : term1501 A B g f x.
Proof. exact (EQ_MP (@lem5090808 A B g f x) (@lem5085016 A B g f x h1)). Qed.
Lemma lem5090814 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (@lem5090811 A B g f x h1 (@lem5090803 A B x a b t s f g y h2 h3)). Qed.
Lemma lem5090815 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5090814 A B x a b t s f g y h1 h2 h3). Qed.
Lemma lem5090817 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090818 : term1440 = False.
Proof. exact (@lem5090817 False). Qed.
Lemma lem5090819 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5090818) (@lem5090815 A B x a b t s f g y h1 h2 h3)). Qed.
Lemma lem5090925 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) (h3 : term586 A B t a s b y) : term392 A B g b s.
Proof. exact (EQ_MP (@lem5087949 A B g t a s b y h2 h3) (@lem5087729 A B x a b t s f g y h1)). Qed.
Lemma lem5090926 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) (h3 : term586 A B t a s b y) : term1502 A B g b s.
Proof. exact (fun h0 : term1377 A B g b s => @lem5090925 A B x f g t a s b y h1 h2 h3). Qed.
Lemma lem5090928 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090929 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) : (term1502 A B g b s) = (term392 A B g b s).
Proof. exact (@lem5090928 (term392 A B g b s)). Qed.
Lemma lem5090930 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) (h3 : term586 A B t a s b y) : term392 A B g b s.
Proof. exact (EQ_MP (@lem5090929 A B g b s) (@lem5090926 A B x f g t a s b y h1 h2 h3)). Qed.
Lemma lem5090933 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5090935 {A B : Type'} (g : B -> A) (b : B) (s : A -> Prop) : (term1377 A B g b s) = (term1503 A B g b s).
Proof. exact (@lem5090933 (term392 A B g b s)). Qed.
Lemma lem5090938 {A B : Type'} (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term605 A B a t g s b y) (h3 : term586 A B t a s b y) : term1503 A B g b s.
Proof. exact (EQ_MP (@lem5090935 A B g b s) (@lem5087991 A B g t a s b y h1 h2 h3)). Qed.
Lemma lem5090941 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : False.
Proof. exact (@lem5090938 A B g t a s b y h1 h3 h4 (@lem5090930 A B x f g t a s b y h2 h3 h4)). Qed.
Lemma lem5090942 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5090941 A B x f g t a s b y h1 h2 h3 h4). Qed.
Lemma lem5090944 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5090945 : term1440 = False.
Proof. exact (@lem5090944 False). Qed.
Lemma lem5091052 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5091053 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5091052 B x). Qed.
Lemma lem5091054 {B : Type'} (b : B) : b = b.
Proof. exact (@lem5091053 B b). Qed.
Lemma lem5091055 {B : Type'} (b : B) : term1441 B b.
Proof. exact (fun h0 : term705 B b => @lem5091054 B b). Qed.
Lemma lem5091057 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091058 {B : Type'} (b : B) : (term1441 B b) = (b = b).
Proof. exact (@lem5091057 (b = b)). Qed.
Lemma lem5091059 {B : Type'} (b : B) : b = b.
Proof. exact (EQ_MP (@lem5091058 B b) (@lem5091055 B b)). Qed.
Lemma lem5091062 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5091064 {B : Type'} (b : B) : (term705 B b) = (term1442 B b).
Proof. exact (@lem5091062 (b = b)). Qed.
Lemma lem5091067 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : term1442 B b.
Proof. exact (EQ_MP (@lem5091064 B b) (@lem5088417 A B t a s b y h1 h2)). Qed.
Lemma lem5091070 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (@lem5091067 A B t a s b y h1 h2 (@lem5091059 B b)). Qed.
Lemma lem5091071 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5091070 A B t a s b y h1 h2). Qed.
Lemma lem5091073 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091074 : term1440 = False.
Proof. exact (@lem5091073 False). Qed.
Lemma lem5091181 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term392 A B g y s.
Proof. exact (EQ_MP (@lem5088579 A B a t g s b y h2) (@lem5085282 A B x a b t s f g y h1)). Qed.
Lemma lem5091182 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term1502 A B g y s.
Proof. exact (fun h0 : term1377 A B g y s => @lem5091181 A B x f a t g s b y h1 h2). Qed.
Lemma lem5091184 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091185 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term1502 A B g y s) = (term392 A B g y s).
Proof. exact (@lem5091184 (term392 A B g y s)). Qed.
Lemma lem5091186 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term392 A B g y s.
Proof. exact (EQ_MP (@lem5091185 A B g y s) (@lem5091182 A B x f a t g s b y h1 h2)). Qed.
Lemma lem5091189 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5091191 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term1377 A B g y s) = (term1503 A B g y s).
Proof. exact (@lem5091189 (term392 A B g y s)). Qed.
Lemma lem5091194 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term1377 A B g y s) : term1503 A B g y s.
Proof. exact (EQ_MP (@lem5091191 A B g y s) (@lem5088636 A B g y s h1)). Qed.
Lemma lem5091197 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (@lem5091194 A B g y s h1 (@lem5091186 A B x f a t g s b y h2 h3)). Qed.
Lemma lem5091198 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5091197 A B x f a t g s b y h1 h2 h3). Qed.
Lemma lem5091200 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091201 : term1440 = False.
Proof. exact (@lem5091200 False). Qed.
Lemma lem5091202 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (EQ_MP (@lem5091201) (@lem5091198 A B x f a t g s b y h1 h2 h3)). Qed.
Lemma lem5091308 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : @IN B y t.
Proof. exact (proj1 (@lem5082089 A B t g s b y h1)). Qed.
Lemma lem5091309 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : term1443 B y t.
Proof. exact (fun h0 : term1365 B y t => @lem5091308 A B t g s b y h1). Qed.
Lemma lem5091311 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091312 {B : Type'} (y : B) (t : B -> Prop) : (term1443 B y t) = (@IN B y t).
Proof. exact (@lem5091311 (@IN B y t)). Qed.
Lemma lem5091313 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : @IN B y t.
Proof. exact (EQ_MP (@lem5091312 B y t) (@lem5091309 A B t g s b y h1)). Qed.
Lemma lem5091315 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5091316 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5091315 A x). Qed.
Lemma lem5091317 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (@lem5091316 A (g y)). Qed.
Lemma lem5091318 {A B : Type'} (g : B -> A) (y : B) : term1504 A B g y.
Proof. exact (fun h0 : term1505 A B g y => @lem5091317 A B g y). Qed.
Lemma lem5091320 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091321 {A B : Type'} (g : B -> A) (y : B) : (term1504 A B g y) = ((g y) = (g y)).
Proof. exact (@lem5091320 ((g y) = (g y))). Qed.
Lemma lem5091322 {A B : Type'} (g : B -> A) (y : B) : (g y) = (g y).
Proof. exact (EQ_MP (@lem5091321 A B g y) (@lem5091318 A B g y)). Qed.
Lemma lem5091328 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5091329 {A B : Type'} (b : B) (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : (term1434 A B t b _65377 g y) = (term1506 A B b t _65377 g y).
Proof. exact (@lem5091328 (_65377 = b) (term1365 B _65377 t) (term1507 A B _65377 g y)). Qed.
Lemma lem5091345 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5091346 {A B : Type'} (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : (term1508 A B t _65377 g y) = (term1509 A B g y _65377 t).
Proof. exact (@lem5091345 (term1507 A B _65377 g y) (term1365 B _65377 t)). Qed.
Lemma lem5091354 {B : Type'} (_65377 : B) (b : B) : (term413 B _65377 b) = (term413 B _65377 b).
Proof. exact (eq_refl (term413 B _65377 b)). Qed.
Lemma lem5091355 {A B : Type'} (b : B) (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : (term1506 A B b t _65377 g y) = (term1510 A B b g y _65377 t).
Proof. exact (MK_COMB (@lem5091354 B _65377 b) (@lem5091346 A B g y _65377 t)). Qed.
Lemma lem5091366 {A B : Type'} (b : B) (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : (term1434 A B t b _65377 g y) = (term1510 A B b g y _65377 t).
Proof. exact (TRANS (@lem5091329 A B b t _65377 g y) (@lem5091355 A B b g y _65377 t)). Qed.
Lemma lem5091367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5091368 {A B : Type'} (b : B) (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : (term1511 A B t b _65377 g y) = (term1512 A B b g y _65377 t).
Proof. exact (MK_COMB (@lem5091367) (@lem5091366 A B b g y _65377 t)). Qed.
Lemma lem5091384 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5091385 {A B : Type'} (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : (term1508 A B t _65377 g y) = (term1509 A B g y _65377 t).
Proof. exact (@lem5091384 (term1507 A B _65377 g y) (term1365 B _65377 t)). Qed.
Lemma lem5091393 {B : Type'} (_65377 : B) (b : B) : (term413 B _65377 b) = (term413 B _65377 b).
Proof. exact (eq_refl (term413 B _65377 b)). Qed.
Lemma lem5091394 {A B : Type'} (b : B) (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : (term1506 A B b t _65377 g y) = (term1510 A B b g y _65377 t).
Proof. exact (MK_COMB (@lem5091393 B _65377 b) (@lem5091385 A B g y _65377 t)). Qed.
Lemma lem5091405 {A B : Type'} (b : B) (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : ((term1434 A B t b _65377 g y) = (term1506 A B b t _65377 g y)) = ((term1510 A B b g y _65377 t) = (term1510 A B b g y _65377 t)).
Proof. exact (MK_COMB (@lem5091368 A B b g y _65377 t) (@lem5091394 A B b g y _65377 t)). Qed.
Lemma lem5091407 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5091408 (x : Prop) : (x = x) = True.
Proof. exact (@lem5091407 Prop x). Qed.
Lemma lem5091409 {A B : Type'} (b : B) (g : B -> A) (y : B) (_65377 : B) (t : B -> Prop) : ((term1510 A B b g y _65377 t) = (term1510 A B b g y _65377 t)) = True.
Proof. exact (@lem5091408 (term1510 A B b g y _65377 t)). Qed.
Lemma lem5091410 {A B : Type'} (b : B) (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : ((term1434 A B t b _65377 g y) = (term1506 A B b t _65377 g y)) = True.
Proof. exact (TRANS (@lem5091405 A B b g y _65377 t) (@lem5091409 A B b g y _65377 t)). Qed.
Lemma lem5091411 {A B : Type'} (b : B) (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : True = ((term1434 A B t b _65377 g y) = (term1506 A B b t _65377 g y)).
Proof. exact (SYM (@lem5091410 A B b t _65377 g y)). Qed.
Lemma lem5091412 {A B : Type'} (b : B) (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : (term1434 A B t b _65377 g y) = (term1506 A B b t _65377 g y).
Proof. exact (EQ_MP (@lem5091411 A B b t _65377 g y) (@lem0)). Qed.
Lemma lem5091413 {A B : Type'} (_65377 : B) (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term1506 A B b t _65377 g y.
Proof. exact (EQ_MP (@lem5091412 A B b t _65377 g y) (@lem5088896 A B _65377 x f a t g s b y h1 h2)). Qed.
Lemma lem5091415 (b : Prop) (a : Prop) : (a \/ b) = (term1453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5091416 {A B : Type'} (t : B -> Prop) (g : B -> A) (y : B) (_65377 : B) (b : B) : (term1506 A B b t _65377 g y) = (term1513 A B t g y _65377 b).
Proof. exact (@lem5091415 (term1508 A B t _65377 g y) (_65377 = b)). Qed.
Lemma lem5091418 (a : Prop) (b : Prop) : (term1455 a b) = (term1456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5091419 {A B : Type'} (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : (term1514 A B t _65377 g y) = (term1515 A B t _65377 g y).
Proof. exact (@lem5091418 (term1365 B _65377 t) (term1507 A B _65377 g y)). Qed.
Lemma lem5091421 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5091422 {B : Type'} (_65377 : B) (t : B -> Prop) : (term1459 B _65377 t) = (@IN B _65377 t).
Proof. exact (@lem5091421 (@IN B _65377 t)). Qed.
Lemma lem5091423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5091424 {B : Type'} (_65377 : B) (t : B -> Prop) : (term1460 B _65377 t) = (term402 B _65377 t).
Proof. exact (MK_COMB (@lem5091423) (@lem5091422 B _65377 t)). Qed.
Lemma lem5091426 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5091427 {A B : Type'} (_65377 : B) (g : B -> A) (y : B) : (term1516 A B _65377 g y) = ((g _65377) = (g y)).
Proof. exact (@lem5091426 ((g _65377) = (g y))). Qed.
Lemma lem5091428 {A B : Type'} (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : (term1515 A B t _65377 g y) = (term1517 A B t _65377 g y).
Proof. exact (MK_COMB (@lem5091424 B _65377 t) (@lem5091427 A B _65377 g y)). Qed.
Lemma lem5091429 {A B : Type'} (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : (term1514 A B t _65377 g y) = (term1517 A B t _65377 g y).
Proof. exact (TRANS (@lem5091419 A B t _65377 g y) (@lem5091428 A B t _65377 g y)). Qed.
Lemma lem5091430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5091431 {A B : Type'} (t : B -> Prop) (_65377 : B) (g : B -> A) (y : B) : (term1518 A B t _65377 g y) = (term1519 A B t _65377 g y).
Proof. exact (MK_COMB (@lem5091430) (@lem5091429 A B t _65377 g y)). Qed.
Lemma lem5091432 {B : Type'} (_65377 : B) (b : B) : (_65377 = b) = (_65377 = b).
Proof. exact (eq_refl (_65377 = b)). Qed.
Lemma lem5091433 {A B : Type'} (t : B -> Prop) (g : B -> A) (y : B) (_65377 : B) (b : B) : (term1513 A B t g y _65377 b) = (term1520 A B t g y _65377 b).
Proof. exact (MK_COMB (@lem5091431 A B t _65377 g y) (@lem5091432 B _65377 b)). Qed.
Lemma lem5091434 {A B : Type'} (t : B -> Prop) (g : B -> A) (y : B) (_65377 : B) (b : B) : (term1506 A B b t _65377 g y) = (term1520 A B t g y _65377 b).
Proof. exact (TRANS (@lem5091416 A B t g y _65377 b) (@lem5091433 A B t g y _65377 b)). Qed.
Lemma lem5091436 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : term1521 A B t g y.
Proof. exact (conj (@lem5091313 A B t g s b y h1) (@lem5091322 A B g y)). Qed.
Lemma lem5091438 {A B : Type'} (_65377 : B) (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term1520 A B t g y _65377 b.
Proof. exact (EQ_MP (@lem5091434 A B t g y _65377 b) (@lem5091413 A B _65377 x f a t g s b y h1 h2)). Qed.
Lemma lem5091439 {A B : Type'} (_65377 : B) (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term1520 A B t g y _65377 b.
Proof. exact (@lem5091438 A B _65377 x f a t g s b y h1 h2). Qed.
Lemma lem5091440 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : term1522 A B t g y b.
Proof. exact (@lem5091439 A B y x f a t g s b y h1 h2). Qed.
Lemma lem5091443 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : y = b.
Proof. exact (@lem5091440 A B x f a t g s b y h2 h3 (@lem5091436 A B t g s b y h1)). Qed.
Lemma lem5091444 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : term1468 B y b.
Proof. exact (fun h0 : term506 B y b => @lem5091443 A B x f a t g s b y h1 h2 h3). Qed.
Lemma lem5091446 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091447 {B : Type'} (y : B) (b : B) : (term1468 B y b) = (y = b).
Proof. exact (@lem5091446 (y = b)). Qed.
Lemma lem5091448 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : y = b.
Proof. exact (EQ_MP (@lem5091447 B y b) (@lem5091444 A B x f a t g s b y h1 h2 h3)). Qed.
Lemma lem5091451 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5091453 {B : Type'} (y : B) (b : B) : (term506 B y b) = (term1469 B y b).
Proof. exact (@lem5091451 (y = b)). Qed.
Lemma lem5091456 {A B : Type'} (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) : term1469 B y b.
Proof. exact (EQ_MP (@lem5091453 B y b) (@lem5088827 A B t g s b y h1)). Qed.
Lemma lem5091459 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (@lem5091456 A B t g s b y h1 (@lem5091448 A B x f a t g s b y h1 h2 h3)). Qed.
Lemma lem5091460 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5091459 A B x f a t g s b y h1 h2 h3). Qed.
Lemma lem5091462 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091463 : term1440 = False.
Proof. exact (@lem5091462 False). Qed.
Lemma lem5091570 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN A a s.
Proof. exact (proj1 (@lem5082031 A B x a b t s f g y h1)). Qed.
Lemma lem5091571 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1443 A a s.
Proof. exact (fun h0 : term1365 A a s => @lem5091570 A B x a b t s f g y h1). Qed.
Lemma lem5091573 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091574 {A : Type'} (a : A) (s : A -> Prop) : (term1443 A a s) = (@IN A a s).
Proof. exact (@lem5091573 (@IN A a s)). Qed.
Lemma lem5091575 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : @IN A a s.
Proof. exact (EQ_MP (@lem5091574 A a s) (@lem5091571 A B x a b t s f g y h1)). Qed.
Lemma lem5091578 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5091580 {A : Type'} (a : A) (s : A -> Prop) : (term1365 A a s) = (term1470 A a s).
Proof. exact (@lem5091578 (@IN A a s)). Qed.
Lemma lem5091583 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1365 A a s) : term1470 A a s.
Proof. exact (EQ_MP (@lem5091580 A a s) (@lem5089073 A a s h1)). Qed.
Lemma lem5091586 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (@lem5091583 A a s h1 (@lem5091575 A B x a b t s f g y h2)). Qed.
Lemma lem5091587 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5091586 A B x a b t s f g y h1 h2). Qed.
Lemma lem5091589 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091590 : term1440 = False.
Proof. exact (@lem5091589 False). Qed.
Lemma lem5091591 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5091590) (@lem5091587 A B x a b t s f g y h1 h2)). Qed.
Lemma lem5091697 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5091698 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5091697 B x). Qed.
Lemma lem5091699 {B : Type'} (b : B) : b = b.
Proof. exact (@lem5091698 B b). Qed.
Lemma lem5091700 {B : Type'} (b : B) : term1441 B b.
Proof. exact (fun h0 : term705 B b => @lem5091699 B b). Qed.
Lemma lem5091702 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091703 {B : Type'} (b : B) : (term1441 B b) = (b = b).
Proof. exact (@lem5091702 (b = b)). Qed.
Lemma lem5091704 {B : Type'} (b : B) : b = b.
Proof. exact (EQ_MP (@lem5091703 B b) (@lem5091700 B b)). Qed.
Lemma lem5091707 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5091709 {B : Type'} (b : B) : (term705 B b) = (term1442 B b).
Proof. exact (@lem5091707 (b = b)). Qed.
Lemma lem5091712 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : term1442 B b.
Proof. exact (EQ_MP (@lem5091709 B b) (@lem5089294 A B t a s b y h1 h2)). Qed.
Lemma lem5091715 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (@lem5091712 A B t a s b y h1 h2 (@lem5091704 B b)). Qed.
Lemma lem5091716 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5091715 A B t a s b y h1 h2). Qed.
Lemma lem5091718 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091719 : term1440 = False.
Proof. exact (@lem5091718 False). Qed.
Lemma lem5091826 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : @IN B y t.
Proof. exact (proj1 (@lem5082105 A B b t s f g y h1)). Qed.
Lemma lem5091827 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term1443 B y t.
Proof. exact (fun h0 : term1365 B y t => @lem5091826 A B b t s f g y h1). Qed.
Lemma lem5091829 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091830 {B : Type'} (y : B) (t : B -> Prop) : (term1443 B y t) = (@IN B y t).
Proof. exact (@lem5091829 (@IN B y t)). Qed.
Lemma lem5091831 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : @IN B y t.
Proof. exact (EQ_MP (@lem5091830 B y t) (@lem5091827 A B b t s f g y h1)). Qed.
Lemma lem5091833 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term506 B y b.
Proof. exact (proj1 (@lem5082098 A B b t s f g y h1)). Qed.
Lemma lem5091834 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term1471 B y b.
Proof. exact (fun h0 : y = b => @lem5091833 A B b t s f g y h1). Qed.
Lemma lem5091836 (p : Prop) : (term1472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5091837 {B : Type'} (y : B) (b : B) : (term1471 B y b) = (term506 B y b).
Proof. exact (@lem5091836 (y = b)). Qed.
Lemma lem5091838 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term506 B y b.
Proof. exact (EQ_MP (@lem5091837 B y b) (@lem5091834 A B b t s f g y h1)). Qed.
Lemma lem5091844 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5091845 {A B : Type'} (b : B) (t : B -> Prop) (g : B -> A) (_65383 : B) (s : A -> Prop) : (term1398 A B t b g _65383 s) = (term1523 A B b t g _65383 s).
Proof. exact (@lem5091844 (_65383 = b) (term1365 B _65383 t) (term392 A B g _65383 s)). Qed.
Lemma lem5091861 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5091862 {A B : Type'} (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : (term1524 A B t g _65383 s) = (term1525 A B g s _65383 t).
Proof. exact (@lem5091861 (term392 A B g _65383 s) (term1365 B _65383 t)). Qed.
Lemma lem5091868 {B : Type'} (_65383 : B) (b : B) : (term413 B _65383 b) = (term413 B _65383 b).
Proof. exact (eq_refl (term413 B _65383 b)). Qed.
Lemma lem5091869 {A B : Type'} (b : B) (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : (term1523 A B b t g _65383 s) = (term1526 A B b g s _65383 t).
Proof. exact (MK_COMB (@lem5091868 B _65383 b) (@lem5091862 A B g s _65383 t)). Qed.
Lemma lem5091880 {A B : Type'} (b : B) (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : (term1398 A B t b g _65383 s) = (term1526 A B b g s _65383 t).
Proof. exact (TRANS (@lem5091845 A B b t g _65383 s) (@lem5091869 A B b g s _65383 t)). Qed.
Lemma lem5091881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5091882 {A B : Type'} (b : B) (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : (term1527 A B t b g _65383 s) = (term1528 A B b g s _65383 t).
Proof. exact (MK_COMB (@lem5091881) (@lem5091880 A B b g s _65383 t)). Qed.
Lemma lem5091896 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5091897 {B : Type'} (b : B) (_65383 : B) (t : B -> Prop) : (term504 B t _65383 b) = (term1479 B b _65383 t).
Proof. exact (@lem5091896 (_65383 = b) (term1365 B _65383 t)). Qed.
Lemma lem5091905 {A B : Type'} (g : B -> A) (_65383 : B) (s : A -> Prop) : (term1529 A B g _65383 s) = (term1529 A B g _65383 s).
Proof. exact (eq_refl (term1529 A B g _65383 s)). Qed.
Lemma lem5091906 {A B : Type'} (g : B -> A) (s : A -> Prop) (b : B) (_65383 : B) (t : B -> Prop) : (term1530 A B g s t _65383 b) = (term1531 A B g s b _65383 t).
Proof. exact (MK_COMB (@lem5091905 A B g _65383 s) (@lem5091897 B b _65383 t)). Qed.
Lemma lem5091910 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5091911 {A B : Type'} (b : B) (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : (term1531 A B g s b _65383 t) = (term1526 A B b g s _65383 t).
Proof. exact (@lem5091910 (_65383 = b) (term392 A B g _65383 s) (term1365 B _65383 t)). Qed.
Lemma lem5091929 {A B : Type'} (b : B) (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : (term1530 A B g s t _65383 b) = (term1526 A B b g s _65383 t).
Proof. exact (TRANS (@lem5091906 A B g s b _65383 t) (@lem5091911 A B b g s _65383 t)). Qed.
Lemma lem5091930 {A B : Type'} (b : B) (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : ((term1398 A B t b g _65383 s) = (term1530 A B g s t _65383 b)) = ((term1526 A B b g s _65383 t) = (term1526 A B b g s _65383 t)).
Proof. exact (MK_COMB (@lem5091882 A B b g s _65383 t) (@lem5091929 A B b g s _65383 t)). Qed.
Lemma lem5091932 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5091933 (x : Prop) : (x = x) = True.
Proof. exact (@lem5091932 Prop x). Qed.
Lemma lem5091934 {A B : Type'} (b : B) (g : B -> A) (s : A -> Prop) (_65383 : B) (t : B -> Prop) : ((term1526 A B b g s _65383 t) = (term1526 A B b g s _65383 t)) = True.
Proof. exact (@lem5091933 (term1526 A B b g s _65383 t)). Qed.
Lemma lem5091935 {A B : Type'} (g : B -> A) (s : A -> Prop) (t : B -> Prop) (_65383 : B) (b : B) : ((term1398 A B t b g _65383 s) = (term1530 A B g s t _65383 b)) = True.
Proof. exact (TRANS (@lem5091930 A B b g s _65383 t) (@lem5091934 A B b g s _65383 t)). Qed.
Lemma lem5091936 {A B : Type'} (g : B -> A) (s : A -> Prop) (t : B -> Prop) (_65383 : B) (b : B) : True = ((term1398 A B t b g _65383 s) = (term1530 A B g s t _65383 b)).
Proof. exact (SYM (@lem5091935 A B g s t _65383 b)). Qed.
Lemma lem5091937 {A B : Type'} (g : B -> A) (s : A -> Prop) (t : B -> Prop) (_65383 : B) (b : B) : (term1398 A B t b g _65383 s) = (term1530 A B g s t _65383 b).
Proof. exact (EQ_MP (@lem5091936 A B g s t _65383 b) (@lem0)). Qed.
Lemma lem5091938 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1530 A B g s t _65383 b.
Proof. exact (EQ_MP (@lem5091937 A B g s t _65383 b) (@lem5085684 A B _65383 x a b t s f g y h1)). Qed.
Lemma lem5091940 (b : Prop) (a : Prop) : (a \/ b) = (term1453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5091941 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65383 : B) (s : A -> Prop) : (term1530 A B g s t _65383 b) = (term1532 A B t b g _65383 s).
Proof. exact (@lem5091940 (term504 B t _65383 b) (term392 A B g _65383 s)). Qed.
Lemma lem5091943 (a : Prop) (b : Prop) : (term1455 a b) = (term1456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5091944 {B : Type'} (t : B -> Prop) (_65383 : B) (b : B) : (term1484 B t _65383 b) = (term1485 B t _65383 b).
Proof. exact (@lem5091943 (term1365 B _65383 t) (_65383 = b)). Qed.
Lemma lem5091946 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5091947 {B : Type'} (_65383 : B) (t : B -> Prop) : (term1459 B _65383 t) = (@IN B _65383 t).
Proof. exact (@lem5091946 (@IN B _65383 t)). Qed.
Lemma lem5091948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5091949 {B : Type'} (_65383 : B) (t : B -> Prop) : (term1460 B _65383 t) = (term402 B _65383 t).
Proof. exact (MK_COMB (@lem5091948) (@lem5091947 B _65383 t)). Qed.
Lemma lem5091950 {B : Type'} (_65383 : B) (b : B) : (term506 B _65383 b) = (term506 B _65383 b).
Proof. exact (eq_refl (term506 B _65383 b)). Qed.
Lemma lem5091951 {B : Type'} (t : B -> Prop) (_65383 : B) (b : B) : (term1485 B t _65383 b) = (term27 B t _65383 b).
Proof. exact (MK_COMB (@lem5091949 B _65383 t) (@lem5091950 B _65383 b)). Qed.
Lemma lem5091952 {B : Type'} (t : B -> Prop) (_65383 : B) (b : B) : (term1484 B t _65383 b) = (term27 B t _65383 b).
Proof. exact (TRANS (@lem5091944 B t _65383 b) (@lem5091951 B t _65383 b)). Qed.
Lemma lem5091953 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5091954 {B : Type'} (t : B -> Prop) (_65383 : B) (b : B) : (term1486 B t _65383 b) = (term1487 B t _65383 b).
Proof. exact (MK_COMB (@lem5091953) (@lem5091952 B t _65383 b)). Qed.
Lemma lem5091955 {A B : Type'} (g : B -> A) (_65383 : B) (s : A -> Prop) : (term392 A B g _65383 s) = (term392 A B g _65383 s).
Proof. exact (eq_refl (term392 A B g _65383 s)). Qed.
Lemma lem5091956 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65383 : B) (s : A -> Prop) : (term1532 A B t b g _65383 s) = (term1533 A B t b g _65383 s).
Proof. exact (MK_COMB (@lem5091954 B t _65383 b) (@lem5091955 A B g _65383 s)). Qed.
Lemma lem5091957 {A B : Type'} (t : B -> Prop) (b : B) (g : B -> A) (_65383 : B) (s : A -> Prop) : (term1530 A B g s t _65383 b) = (term1533 A B t b g _65383 s).
Proof. exact (TRANS (@lem5091941 A B t b g _65383 s) (@lem5091956 A B t b g _65383 s)). Qed.
Lemma lem5091959 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term27 B t y b.
Proof. exact (conj (@lem5091831 A B b t s f g y h1) (@lem5091838 A B b t s f g y h1)). Qed.
Lemma lem5091961 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1533 A B t b g _65383 s.
Proof. exact (EQ_MP (@lem5091957 A B t b g _65383 s) (@lem5091938 A B _65383 x a b t s f g y h1)). Qed.
Lemma lem5091962 {A B : Type'} (_65383 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1533 A B t b g _65383 s.
Proof. exact (@lem5091961 A B _65383 x a b t s f g y h1). Qed.
Lemma lem5091963 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1533 A B t b g y s.
Proof. exact (@lem5091962 A B y x a b t s f g y h1). Qed.
Lemma lem5091966 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) (h2 : term1177 A B x a b t s f g y) : term392 A B g y s.
Proof. exact (@lem5091963 A B x a b t s f g y h2 (@lem5091959 A B b t s f g y h1)). Qed.
Lemma lem5091967 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) (h2 : term1177 A B x a b t s f g y) : term1502 A B g y s.
Proof. exact (fun h0 : term1377 A B g y s => @lem5091966 A B x a b t s f g y h1 h2). Qed.
Lemma lem5091969 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091970 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term1502 A B g y s) = (term392 A B g y s).
Proof. exact (@lem5091969 (term392 A B g y s)). Qed.
Lemma lem5091971 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) (h2 : term1177 A B x a b t s f g y) : term392 A B g y s.
Proof. exact (EQ_MP (@lem5091970 A B g y s) (@lem5091967 A B x a b t s f g y h1 h2)). Qed.
Lemma lem5091974 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5091976 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term1377 A B g y s) = (term1503 A B g y s).
Proof. exact (@lem5091974 (term392 A B g y s)). Qed.
Lemma lem5091979 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term1377 A B g y s) : term1503 A B g y s.
Proof. exact (EQ_MP (@lem5091976 A B g y s) (@lem5085660 A B g y s h1)). Qed.
Lemma lem5091982 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (@lem5091979 A B g y s h1 (@lem5091971 A B x a b t s f g y h2 h3)). Qed.
Lemma lem5091983 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5091982 A B x a b t s f g y h1 h2 h3). Qed.
Lemma lem5091985 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5091986 : term1440 = False.
Proof. exact (@lem5091985 False). Qed.
Lemma lem5091987 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5091986) (@lem5091983 A B x a b t s f g y h1 h2 h3)). Qed.
Lemma lem5092093 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : @IN B y t.
Proof. exact (proj1 (@lem5082105 A B b t s f g y h1)). Qed.
Lemma lem5092094 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term1443 B y t.
Proof. exact (fun h0 : term1365 B y t => @lem5092093 A B b t s f g y h1). Qed.
Lemma lem5092096 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5092097 {B : Type'} (y : B) (t : B -> Prop) : (term1443 B y t) = (@IN B y t).
Proof. exact (@lem5092096 (@IN B y t)). Qed.
Lemma lem5092098 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : @IN B y t.
Proof. exact (EQ_MP (@lem5092097 B y t) (@lem5092094 A B b t s f g y h1)). Qed.
Lemma lem5092100 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term506 B y b.
Proof. exact (proj1 (@lem5082098 A B b t s f g y h1)). Qed.
Lemma lem5092101 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term1471 B y b.
Proof. exact (fun h0 : y = b => @lem5092100 A B b t s f g y h1). Qed.
Lemma lem5092103 (p : Prop) : (term1472 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5092104 {B : Type'} (y : B) (b : B) : (term1471 B y b) = (term506 B y b).
Proof. exact (@lem5092103 (y = b)). Qed.
Lemma lem5092105 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term506 B y b.
Proof. exact (EQ_MP (@lem5092104 B y b) (@lem5092101 A B b t s f g y h1)). Qed.
Lemma lem5092111 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5092112 {A B : Type'} (b : B) (t : B -> Prop) (f : A -> B) (g : B -> A) (_65385 : B) : (term1399 A B t b f g _65385) = (term1534 A B b t f g _65385).
Proof. exact (@lem5092111 (_65385 = b) (term1365 B _65385 t) ((term124 A B f g _65385) = _65385)). Qed.
Lemma lem5092128 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5092129 {A B : Type'} (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : (term1535 A B t f g _65385) = (term1536 A B f g _65385 t).
Proof. exact (@lem5092128 ((term124 A B f g _65385) = _65385) (term1365 B _65385 t)). Qed.
Lemma lem5092137 {B : Type'} (_65385 : B) (b : B) : (term413 B _65385 b) = (term413 B _65385 b).
Proof. exact (eq_refl (term413 B _65385 b)). Qed.
Lemma lem5092138 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : (term1534 A B b t f g _65385) = (term1537 A B b f g _65385 t).
Proof. exact (MK_COMB (@lem5092137 B _65385 b) (@lem5092129 A B f g _65385 t)). Qed.
Lemma lem5092149 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : (term1399 A B t b f g _65385) = (term1537 A B b f g _65385 t).
Proof. exact (TRANS (@lem5092112 A B b t f g _65385) (@lem5092138 A B b f g _65385 t)). Qed.
Lemma lem5092150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5092151 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : (term1538 A B t b f g _65385) = (term1539 A B b f g _65385 t).
Proof. exact (MK_COMB (@lem5092150) (@lem5092149 A B b f g _65385 t)). Qed.
Lemma lem5092167 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5092168 {B : Type'} (b : B) (_65385 : B) (t : B -> Prop) : (term504 B t _65385 b) = (term1479 B b _65385 t).
Proof. exact (@lem5092167 (_65385 = b) (term1365 B _65385 t)). Qed.
Lemma lem5092176 {A B : Type'} (f : A -> B) (g : B -> A) (_65385 : B) : (term1540 A B f g _65385) = (term1540 A B f g _65385).
Proof. exact (eq_refl (term1540 A B f g _65385)). Qed.
Lemma lem5092177 {A B : Type'} (f : A -> B) (g : B -> A) (b : B) (_65385 : B) (t : B -> Prop) : (term1541 A B f g t _65385 b) = (term1542 A B f g b _65385 t).
Proof. exact (MK_COMB (@lem5092176 A B f g _65385) (@lem5092168 B b _65385 t)). Qed.
Lemma lem5092181 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5092182 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : (term1542 A B f g b _65385 t) = (term1537 A B b f g _65385 t).
Proof. exact (@lem5092181 (_65385 = b) ((term124 A B f g _65385) = _65385) (term1365 B _65385 t)). Qed.
Lemma lem5092202 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : (term1541 A B f g t _65385 b) = (term1537 A B b f g _65385 t).
Proof. exact (TRANS (@lem5092177 A B f g b _65385 t) (@lem5092182 A B b f g _65385 t)). Qed.
Lemma lem5092203 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : ((term1399 A B t b f g _65385) = (term1541 A B f g t _65385 b)) = ((term1537 A B b f g _65385 t) = (term1537 A B b f g _65385 t)).
Proof. exact (MK_COMB (@lem5092151 A B b f g _65385 t) (@lem5092202 A B b f g _65385 t)). Qed.
Lemma lem5092205 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5092206 (x : Prop) : (x = x) = True.
Proof. exact (@lem5092205 Prop x). Qed.
Lemma lem5092207 {A B : Type'} (b : B) (f : A -> B) (g : B -> A) (_65385 : B) (t : B -> Prop) : ((term1537 A B b f g _65385 t) = (term1537 A B b f g _65385 t)) = True.
Proof. exact (@lem5092206 (term1537 A B b f g _65385 t)). Qed.
Lemma lem5092208 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_65385 : B) (b : B) : ((term1399 A B t b f g _65385) = (term1541 A B f g t _65385 b)) = True.
Proof. exact (TRANS (@lem5092203 A B b f g _65385 t) (@lem5092207 A B b f g _65385 t)). Qed.
Lemma lem5092209 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_65385 : B) (b : B) : True = ((term1399 A B t b f g _65385) = (term1541 A B f g t _65385 b)).
Proof. exact (SYM (@lem5092208 A B f g t _65385 b)). Qed.
Lemma lem5092210 {A B : Type'} (f : A -> B) (g : B -> A) (t : B -> Prop) (_65385 : B) (b : B) : (term1399 A B t b f g _65385) = (term1541 A B f g t _65385 b).
Proof. exact (EQ_MP (@lem5092209 A B f g t _65385 b) (@lem0)). Qed.
Lemma lem5092211 {A B : Type'} (_65385 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1541 A B f g t _65385 b.
Proof. exact (EQ_MP (@lem5092210 A B f g t _65385 b) (@lem5085764 A B _65385 x a b t s f g y h1)). Qed.
Lemma lem5092213 (b : Prop) (a : Prop) : (a \/ b) = (term1453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5092214 {A B : Type'} (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (_65385 : B) : (term1541 A B f g t _65385 b) = (term1543 A B t b f g _65385).
Proof. exact (@lem5092213 (term504 B t _65385 b) ((term124 A B f g _65385) = _65385)). Qed.
Lemma lem5092216 (a : Prop) (b : Prop) : (term1455 a b) = (term1456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5092217 {B : Type'} (t : B -> Prop) (_65385 : B) (b : B) : (term1484 B t _65385 b) = (term1485 B t _65385 b).
Proof. exact (@lem5092216 (term1365 B _65385 t) (_65385 = b)). Qed.
Lemma lem5092219 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5092220 {B : Type'} (_65385 : B) (t : B -> Prop) : (term1459 B _65385 t) = (@IN B _65385 t).
Proof. exact (@lem5092219 (@IN B _65385 t)). Qed.
Lemma lem5092221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5092222 {B : Type'} (_65385 : B) (t : B -> Prop) : (term1460 B _65385 t) = (term402 B _65385 t).
Proof. exact (MK_COMB (@lem5092221) (@lem5092220 B _65385 t)). Qed.
Lemma lem5092223 {B : Type'} (_65385 : B) (b : B) : (term506 B _65385 b) = (term506 B _65385 b).
Proof. exact (eq_refl (term506 B _65385 b)). Qed.
Lemma lem5092224 {B : Type'} (t : B -> Prop) (_65385 : B) (b : B) : (term1485 B t _65385 b) = (term27 B t _65385 b).
Proof. exact (MK_COMB (@lem5092222 B _65385 t) (@lem5092223 B _65385 b)). Qed.
Lemma lem5092225 {B : Type'} (t : B -> Prop) (_65385 : B) (b : B) : (term1484 B t _65385 b) = (term27 B t _65385 b).
Proof. exact (TRANS (@lem5092217 B t _65385 b) (@lem5092224 B t _65385 b)). Qed.
Lemma lem5092226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5092227 {B : Type'} (t : B -> Prop) (_65385 : B) (b : B) : (term1486 B t _65385 b) = (term1487 B t _65385 b).
Proof. exact (MK_COMB (@lem5092226) (@lem5092225 B t _65385 b)). Qed.
Lemma lem5092228 {A B : Type'} (f : A -> B) (g : B -> A) (_65385 : B) : ((term124 A B f g _65385) = _65385) = ((term124 A B f g _65385) = _65385).
Proof. exact (eq_refl ((term124 A B f g _65385) = _65385)). Qed.
Lemma lem5092229 {A B : Type'} (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (_65385 : B) : (term1543 A B t b f g _65385) = (term1544 A B t b f g _65385).
Proof. exact (MK_COMB (@lem5092227 B t _65385 b) (@lem5092228 A B f g _65385)). Qed.
Lemma lem5092230 {A B : Type'} (t : B -> Prop) (b : B) (f : A -> B) (g : B -> A) (_65385 : B) : (term1541 A B f g t _65385 b) = (term1544 A B t b f g _65385).
Proof. exact (TRANS (@lem5092214 A B t b f g _65385) (@lem5092229 A B t b f g _65385)). Qed.
Lemma lem5092232 {A B : Type'} (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) : term27 B t y b.
Proof. exact (conj (@lem5092098 A B b t s f g y h1) (@lem5092105 A B b t s f g y h1)). Qed.
Lemma lem5092234 {A B : Type'} (_65385 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1544 A B t b f g _65385.
Proof. exact (EQ_MP (@lem5092230 A B t b f g _65385) (@lem5092211 A B _65385 x a b t s f g y h1)). Qed.
Lemma lem5092235 {A B : Type'} (_65385 : B) (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1544 A B t b f g _65385.
Proof. exact (@lem5092234 A B _65385 x a b t s f g y h1). Qed.
Lemma lem5092236 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : term1544 A B t b f g y.
Proof. exact (@lem5092235 A B y x a b t s f g y h1). Qed.
Lemma lem5092239 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) (h2 : term1177 A B x a b t s f g y) : (term124 A B f g y) = y.
Proof. exact (@lem5092236 A B x a b t s f g y h2 (@lem5092232 A B b t s f g y h1)). Qed.
Lemma lem5092240 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) (h2 : term1177 A B x a b t s f g y) : term1545 A B f g y.
Proof. exact (fun h0 : term1387 A B f g y => @lem5092239 A B x a b t s f g y h1 h2). Qed.
Lemma lem5092242 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5092243 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term1545 A B f g y) = ((term124 A B f g y) = y).
Proof. exact (@lem5092242 ((term124 A B f g y) = y)). Qed.
Lemma lem5092244 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) (h2 : term1177 A B x a b t s f g y) : (term124 A B f g y) = y.
Proof. exact (EQ_MP (@lem5092243 A B f g y) (@lem5092240 A B x a b t s f g y h1 h2)). Qed.
Lemma lem5092247 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5092249 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term1387 A B f g y) = (term1546 A B f g y).
Proof. exact (@lem5092247 ((term124 A B f g y) = y)). Qed.
Lemma lem5092252 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) : term1546 A B f g y.
Proof. exact (EQ_MP (@lem5092249 A B f g y) (@lem5085752 A B f g y h1)). Qed.
Lemma lem5092255 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (@lem5092252 A B f g y h1 (@lem5092244 A B x a b t s f g y h2 h3)). Qed.
Lemma lem5092256 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : term1440.
Proof. exact (fun h0 : ~ False => @lem5092255 A B x a b t s f g y h1 h2 h3). Qed.
Lemma lem5092258 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5092259 : term1440 = False.
Proof. exact (@lem5092258 False). Qed.
Lemma lem5092260 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092259) (@lem5092256 A B x a b t s f g y h1 h2 h3)). Qed.
Lemma lem5092366 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5092367 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5092366 A x). Qed.
Lemma lem5092368 {A : Type'} (a : A) : a = a.
Proof. exact (@lem5092367 A a). Qed.
Lemma lem5092369 {A : Type'} (a : A) : term1441 A a.
Proof. exact (fun h0 : term705 A a => @lem5092368 A a). Qed.
Lemma lem5092371 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5092372 {A : Type'} (a : A) : (term1441 A a) = (a = a).
Proof. exact (@lem5092371 (a = a)). Qed.
Lemma lem5092373 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem5092372 A a) (@lem5092369 A a)). Qed.
Lemma lem5092376 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5092378 {A : Type'} (a : A) : (term705 A a) = (term1442 A a).
Proof. exact (@lem5092376 (a = a)). Qed.
Lemma lem5092381 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1238 A B t b s a f g) : term1442 A a.
Proof. exact (EQ_MP (@lem5092378 A a) (@lem5085826 A B t b s a f g h1)). Qed.
Lemma lem5092384 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1238 A B t b s a f g) : False.
Proof. exact (@lem5092381 A B t b s a f g h1 (@lem5092373 A a)). Qed.
Lemma lem5092385 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1238 A B t b s a f g) : term1440.
Proof. exact (fun h0 : ~ False => @lem5092384 A B t b s a f g h1). Qed.
Lemma lem5092387 (p : Prop) : (term1438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5092388 : term1440 = False.
Proof. exact (@lem5092387 False). Qed.
Lemma lem5092389 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1238 A B t b s a f g) : False.
Proof. exact (EQ_MP (@lem5092388) (@lem5092385 A B t b s a f g h1)). Qed.
Lemma lem5092390 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5091719) (@lem5091716 A B t a s b y h1 h2)). Qed.
Lemma lem5092391 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h3 : term1365 A a s => @lem5091591 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5089073 A a s h1)). Qed.
Lemma lem5092393 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092391 A B x a b t s f g y h1 h2) (@lem5089073 A a s h1)). Qed.
Lemma lem5092394 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (EQ_MP (@lem5091463) (@lem5091460 A B x f a t g s b y h1 h2 h3)). Qed.
Lemma lem5092395 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : (term1377 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term1377 A B g y s => @lem5091202 A B x f a t g s b y h1 h2 h3) (fun h4 : False => @lem5088636 A B g y s h1)). Qed.
Lemma lem5092397 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (EQ_MP (@lem5092395 A B x f a t g s b y h1 h2 h3) (@lem5088636 A B g y s h1)). Qed.
Lemma lem5092399 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5091074) (@lem5091071 A B t a s b y h1 h2)). Qed.
Lemma lem5092400 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5090945) (@lem5090942 A B x f g t a s b y h1 h2 h3 h4)). Qed.
Lemma lem5092401 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h5 : term1365 A a s => @lem5092400 A B x f g t a s b y h1 h2 h3 h4) (fun h5 : False => @lem5087783 A a s h1)). Qed.
Lemma lem5092403 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092401 A B x f g t a s b y h1 h2 h3 h4) (@lem5087783 A a s h1)). Qed.
Lemma lem5092404 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5090278) (@lem5090275 A B s b t a x h1 h2)). Qed.
Lemma lem5092405 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h3 : term1365 B b t => @lem5090150 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5087340 B b t h1)). Qed.
Lemma lem5092407 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092405 A B x a b t s f g y h1 h2) (@lem5087340 B b t h1)). Qed.
Lemma lem5092408 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5090022) (@lem5090019 A B g y b s f t a x h1 h2 h3)). Qed.
Lemma lem5092409 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : (term1366 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term1366 A B f x t => @lem5089761 A B g y b s f t a x h1 h2 h3) (fun h4 : False => @lem5086902 A B f x t h1)). Qed.
Lemma lem5092411 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092409 A B g y b s f t a x h1 h2 h3) (@lem5086902 A B f x t h1)). Qed.
Lemma lem5092413 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5089633) (@lem5089630 A B s b t a x h1 h2)). Qed.
Lemma lem5092414 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5089504) (@lem5089501 A B g y b s f t a x h1 h2 h3 h4)). Qed.
Lemma lem5092415 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h5 : term1365 B b t => @lem5092414 A B g y b s f t a x h1 h2 h3 h4) (fun h5 : False => @lem5086046 B b t h1)). Qed.
Lemma lem5092417 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092415 A B g y b s f t a x h1 h2 h3 h4) (@lem5086046 B b t h1)). Qed.
Lemma lem5092418 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : (term1387 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term1387 A B f g y => @lem5092260 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5085752 A B f g y h1)). Qed.
Lemma lem5092419 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092418 A B x a b t s f g y h1 h2 h3) (@lem5085752 A B f g y h1)). Qed.
Lemma lem5092420 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : (term1377 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term1377 A B g y s => @lem5091987 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5085660 A B g y s h1)). Qed.
Lemma lem5092421 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092420 A B x a b t s f g y h1 h2 h3) (@lem5085660 A B g y s h1)). Qed.
Lemma lem5092422 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : (term506 B b y) = False.
Proof. exact (prop_ext (fun h3 : term506 B b y => @lem5092390 A B t a s b y h1 h2) (fun h3 : False => @lem5085568 B b y h1)). Qed.
Lemma lem5092423 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092422 A B t a s b y h1 h2) (@lem5085568 B b y h1)). Qed.
Lemma lem5092424 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h3 : term1365 A a s => @lem5092393 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5085476 A a s h1)). Qed.
Lemma lem5092425 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092424 A B x a b t s f g y h1 h2) (@lem5085476 A a s h1)). Qed.
Lemma lem5092426 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : (term1377 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term1377 A B g y s => @lem5092397 A B x f a t g s b y h1 h2 h3) (fun h4 : False => @lem5085292 A B g y s h1)). Qed.
Lemma lem5092427 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (EQ_MP (@lem5092426 A B x f a t g s b y h1 h2 h3) (@lem5085292 A B g y s h1)). Qed.
Lemma lem5092428 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : (term506 B b y) = False.
Proof. exact (prop_ext (fun h3 : term506 B b y => @lem5092399 A B t a s b y h1 h2) (fun h3 : False => @lem5085200 B b y h1)). Qed.
Lemma lem5092429 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092428 A B t a s b y h1 h2) (@lem5085200 B b y h1)). Qed.
Lemma lem5092430 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h5 : term1365 A a s => @lem5092403 A B x f g t a s b y h1 h2 h3 h4) (fun h5 : False => @lem5085108 A a s h1)). Qed.
Lemma lem5092431 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092430 A B x f g t a s b y h1 h2 h3 h4) (@lem5085108 A a s h1)). Qed.
Lemma lem5092432 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : (term1376 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term1376 A B g f x => @lem5090819 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5085016 A B g f x h1)). Qed.
Lemma lem5092433 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092432 A B x a b t s f g y h1 h2 h3) (@lem5085016 A B g f x h1)). Qed.
Lemma lem5092434 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : (term1366 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term1366 A B f x t => @lem5090546 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5084924 A B f x t h1)). Qed.
Lemma lem5092435 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092434 A B x a b t s f g y h1 h2 h3) (@lem5084924 A B f x t h1)). Qed.
Lemma lem5092436 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : (term506 A a x) = False.
Proof. exact (prop_ext (fun h3 : term506 A a x => @lem5092404 A B s b t a x h1 h2) (fun h3 : False => @lem5084832 A a x h1)). Qed.
Lemma lem5092437 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5092436 A B s b t a x h1 h2) (@lem5084832 A a x h1)). Qed.
Lemma lem5092438 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h3 : term1365 B b t => @lem5092407 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5084740 B b t h1)). Qed.
Lemma lem5092439 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092438 A B x a b t s f g y h1 h2) (@lem5084740 B b t h1)). Qed.
Lemma lem5092440 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : (term1366 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term1366 A B f x t => @lem5092411 A B g y b s f t a x h1 h2 h3) (fun h4 : False => @lem5084556 A B f x t h1)). Qed.
Lemma lem5092441 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092440 A B g y b s f t a x h1 h2 h3) (@lem5084556 A B f x t h1)). Qed.
Lemma lem5092442 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : (term506 A a x) = False.
Proof. exact (prop_ext (fun h3 : term506 A a x => @lem5092413 A B s b t a x h1 h2) (fun h3 : False => @lem5084464 A a x h1)). Qed.
Lemma lem5092443 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5092442 A B s b t a x h1 h2) (@lem5084464 A a x h1)). Qed.
Lemma lem5092444 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h5 : term1365 B b t => @lem5092417 A B g y b s f t a x h1 h2 h3 h4) (fun h5 : False => @lem5084372 B b t h1)). Qed.
Lemma lem5092445 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092444 A B g y b s f t a x h1 h2 h3 h4) (@lem5084372 B b t h1)). Qed.
Lemma lem5092446 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : (term1387 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term1387 A B f g y => @lem5092419 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5084012 A B f g y h1)). Qed.
Lemma lem5092447 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092446 A B x a b t s f g y h1 h2 h3) (@lem5084012 A B f g y h1)). Qed.
Lemma lem5092448 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : (term1377 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term1377 A B g y s => @lem5092421 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5083894 A B g y s h1)). Qed.
Lemma lem5092449 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092448 A B x a b t s f g y h1 h2 h3) (@lem5083894 A B g y s h1)). Qed.
Lemma lem5092450 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : (term506 B b y) = False.
Proof. exact (prop_ext (fun h3 : term506 B b y => @lem5092423 A B t a s b y h1 h2) (fun h3 : False => @lem5083776 B b y h1)). Qed.
Lemma lem5092451 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092450 A B t a s b y h1 h2) (@lem5083776 B b y h1)). Qed.
Lemma lem5092452 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h3 : term1365 A a s => @lem5092425 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5083658 A a s h1)). Qed.
Lemma lem5092453 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092452 A B x a b t s f g y h1 h2) (@lem5083658 A a s h1)). Qed.
Lemma lem5092454 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : (term1377 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term1377 A B g y s => @lem5092427 A B x f a t g s b y h1 h2 h3) (fun h4 : False => @lem5083422 A B g y s h1)). Qed.
Lemma lem5092455 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (EQ_MP (@lem5092454 A B x f a t g s b y h1 h2 h3) (@lem5083422 A B g y s h1)). Qed.
Lemma lem5092456 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : (term506 B b y) = False.
Proof. exact (prop_ext (fun h3 : term506 B b y => @lem5092429 A B t a s b y h1 h2) (fun h3 : False => @lem5083304 B b y h1)). Qed.
Lemma lem5092457 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092456 A B t a s b y h1 h2) (@lem5083304 B b y h1)). Qed.
Lemma lem5092458 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h5 : term1365 A a s => @lem5092431 A B x f g t a s b y h1 h2 h3 h4) (fun h5 : False => @lem5083186 A a s h1)). Qed.
Lemma lem5092459 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092458 A B x f g t a s b y h1 h2 h3 h4) (@lem5083186 A a s h1)). Qed.
Lemma lem5092460 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : (term1376 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term1376 A B g f x => @lem5092433 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5083068 A B g f x h1)). Qed.
Lemma lem5092461 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092460 A B x a b t s f g y h1 h2 h3) (@lem5083068 A B g f x h1)). Qed.
Lemma lem5092462 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : (term1366 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term1366 A B f x t => @lem5092435 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5082950 A B f x t h1)). Qed.
Lemma lem5092463 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092462 A B x a b t s f g y h1 h2 h3) (@lem5082950 A B f x t h1)). Qed.
Lemma lem5092464 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : (term506 A a x) = False.
Proof. exact (prop_ext (fun h3 : term506 A a x => @lem5092437 A B s b t a x h1 h2) (fun h3 : False => @lem5082832 A a x h1)). Qed.
Lemma lem5092465 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5092464 A B s b t a x h1 h2) (@lem5082832 A a x h1)). Qed.
Lemma lem5092466 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h3 : term1365 B b t => @lem5092439 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5082714 B b t h1)). Qed.
Lemma lem5092467 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092466 A B x a b t s f g y h1 h2) (@lem5082714 B b t h1)). Qed.
Lemma lem5092468 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : (term1366 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term1366 A B f x t => @lem5092441 A B g y b s f t a x h1 h2 h3) (fun h4 : False => @lem5082478 A B f x t h1)). Qed.
Lemma lem5092469 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092468 A B g y b s f t a x h1 h2 h3) (@lem5082478 A B f x t h1)). Qed.
Lemma lem5092470 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : (term506 A a x) = False.
Proof. exact (prop_ext (fun h3 : term506 A a x => @lem5092443 A B s b t a x h1 h2) (fun h3 : False => @lem5082360 A a x h1)). Qed.
Lemma lem5092471 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5092470 A B s b t a x h1 h2) (@lem5082360 A a x h1)). Qed.
Lemma lem5092472 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h5 : term1365 B b t => @lem5092445 A B g y b s f t a x h1 h2 h3 h4) (fun h5 : False => @lem5082242 B b t h1)). Qed.
Lemma lem5092473 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092472 A B g y b s f t a x h1 h2 h3 h4) (@lem5082242 B b t h1)). Qed.
Lemma lem5092474 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : (term1387 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term1387 A B f g y => @lem5092447 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5084012 A B f g y h1)). Qed.
Lemma lem5092475 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1387 A B f g y) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092474 A B x a b t s f g y h1 h2 h3) (@lem5084012 A B f g y h1)). Qed.
Lemma lem5092476 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : (term1377 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term1377 A B g y s => @lem5092449 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5083894 A B g y s h1)). Qed.
Lemma lem5092477 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1377 A B g y s) (h2 : term614 A B b t s f g y) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092476 A B x a b t s f g y h1 h2 h3) (@lem5083894 A B g y s h1)). Qed.
Lemma lem5092478 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : (term506 B b y) = False.
Proof. exact (prop_ext (fun h3 : term506 B b y => @lem5092451 A B t a s b y h1 h2) (fun h3 : False => @lem5083776 B b y h1)). Qed.
Lemma lem5092479 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092478 A B t a s b y h1 h2) (@lem5083776 B b y h1)). Qed.
Lemma lem5092480 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h3 : term1365 A a s => @lem5092453 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5083658 A a s h1)). Qed.
Lemma lem5092481 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092480 A B x a b t s f g y h1 h2) (@lem5083658 A a s h1)). Qed.
Lemma lem5092482 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : (term1377 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term1377 A B g y s => @lem5092455 A B x f a t g s b y h1 h2 h3) (fun h4 : False => @lem5083422 A B g y s h1)). Qed.
Lemma lem5092483 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1377 A B g y s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (EQ_MP (@lem5092482 A B x f a t g s b y h1 h2 h3) (@lem5083422 A B g y s h1)). Qed.
Lemma lem5092484 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : (term506 B b y) = False.
Proof. exact (prop_ext (fun h3 : term506 B b y => @lem5092457 A B t a s b y h1 h2) (fun h3 : False => @lem5083304 B b y h1)). Qed.
Lemma lem5092485 {A B : Type'} (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term506 B b y) (h2 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092484 A B t a s b y h1 h2) (@lem5083304 B b y h1)). Qed.
Lemma lem5092486 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : (term1365 A a s) = False.
Proof. exact (prop_ext (fun h5 : term1365 A a s => @lem5092459 A B x f g t a s b y h1 h2 h3 h4) (fun h5 : False => @lem5083186 A a s h1)). Qed.
Lemma lem5092487 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1365 A a s) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) (h4 : term586 A B t a s b y) : False.
Proof. exact (EQ_MP (@lem5092486 A B x f g t a s b y h1 h2 h3 h4) (@lem5083186 A a s h1)). Qed.
Lemma lem5092488 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : (term1376 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term1376 A B g f x => @lem5092461 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5083068 A B g f x h1)). Qed.
Lemma lem5092489 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1376 A B g f x) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092488 A B x a b t s f g y h1 h2 h3) (@lem5083068 A B g f x h1)). Qed.
Lemma lem5092490 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : (term1366 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term1366 A B f x t => @lem5092463 A B x a b t s f g y h1 h2 h3) (fun h4 : False => @lem5082950 A B f x t h1)). Qed.
Lemma lem5092491 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1366 A B f x t) (h2 : term554 A B a s t g f x) (h3 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092490 A B x a b t s f g y h1 h2 h3) (@lem5082950 A B f x t h1)). Qed.
Lemma lem5092492 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : (term506 A a x) = False.
Proof. exact (prop_ext (fun h3 : term506 A a x => @lem5092465 A B s b t a x h1 h2) (fun h3 : False => @lem5082832 A a x h1)). Qed.
Lemma lem5092493 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5092492 A B s b t a x h1 h2) (@lem5082832 A a x h1)). Qed.
Lemma lem5092494 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h3 : term1365 B b t => @lem5092467 A B x a b t s f g y h1 h2) (fun h3 : False => @lem5082714 B b t h1)). Qed.
Lemma lem5092495 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (EQ_MP (@lem5092494 A B x a b t s f g y h1 h2) (@lem5082714 B b t h1)). Qed.
Lemma lem5092496 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : (term1366 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term1366 A B f x t => @lem5092469 A B g y b s f t a x h1 h2 h3) (fun h4 : False => @lem5082478 A B f x t h1)). Qed.
Lemma lem5092497 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1366 A B f x t) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092496 A B g y b s f t a x h1 h2 h3) (@lem5082478 A B f x t h1)). Qed.
Lemma lem5092498 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : (term506 A a x) = False.
Proof. exact (prop_ext (fun h3 : term506 A a x => @lem5092471 A B s b t a x h1 h2) (fun h3 : False => @lem5082360 A a x h1)). Qed.
Lemma lem5092499 {A B : Type'} (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term506 A a x) (h2 : term526 A B s b t a x) : False.
Proof. exact (EQ_MP (@lem5092498 A B s b t a x h1 h2) (@lem5082360 A a x h1)). Qed.
Lemma lem5092500 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : (term1365 B b t) = False.
Proof. exact (prop_ext (fun h5 : term1365 B b t => @lem5092473 A B g y b s f t a x h1 h2 h3 h4) (fun h5 : False => @lem5082242 B b t h1)). Qed.
Lemma lem5092501 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1365 B b t) (h2 : term1177 A B x a b t s f g y) (h3 : term526 A B s b t a x) (h4 : term545 A B b s f t a x) : False.
Proof. exact (EQ_MP (@lem5092500 A B g y b s f t a x h1 h2 h3 h4) (@lem5082242 B b t h1)). Qed.
Lemma lem5092502 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term614 A B b t s f g y) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (or_elim (@lem5082107 A B b t s f g y h1) (fun h0 : term1377 A B g y s => @lem5092477 A B x a b t s f g y h0 h1 h2) (fun h0 : term1387 A B f g y => @lem5092475 A B x a b t s f g y h0 h1 h2)). Qed.
Lemma lem5092503 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term586 A B t a s b y) : False.
Proof. exact (or_elim (@lem5082101 A B t a s b y h2) (fun h0 : term1365 A a s => @lem5092481 A B x a b t s f g y h0 h1) (fun h0 : term506 B b y => @lem5092479 A B t a s b y h0 h2)). Qed.
Lemma lem5092504 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term621 A B a b t s f g y) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (or_elim (@lem5082095 A B a b t s f g y h1) (fun h0 : term586 A B t a s b y => @lem5092503 A B x f g t a s b y h2 h0) (fun h0 : term614 A B b t s f g y => @lem5092502 A B x a b t s f g y h0 h2)). Qed.
Lemma lem5092505 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term594 A B t g s b y) (h2 : term1177 A B x a b t s f g y) (h3 : term605 A B a t g s b y) : False.
Proof. exact (or_elim (@lem5082091 A B t g s b y h1) (fun h0 : term1377 A B g y s => @lem5092483 A B x f a t g s b y h0 h2 h3) (fun h0 : term506 B b y => @lem5092394 A B x f a t g s b y h1 h2 h3)). Qed.
Lemma lem5092506 {A B : Type'} (x : A) (f : A -> B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) (h3 : term586 A B t a s b y) : False.
Proof. exact (or_elim (@lem5082085 A B t a s b y h3) (fun h0 : term1365 A a s => @lem5092487 A B x f g t a s b y h0 h1 h2 h3) (fun h0 : term506 B b y => @lem5092485 A B t a s b y h0 h3)). Qed.
Lemma lem5092507 {A B : Type'} (x : A) (f : A -> B) (a : A) (t : B -> Prop) (g : B -> A) (s : A -> Prop) (b : B) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term605 A B a t g s b y) : False.
Proof. exact (or_elim (@lem5082079 A B a t g s b y h2) (fun h0 : term586 A B t a s b y => @lem5092506 A B x f g t a s b y h1 h2 h0) (fun h0 : term594 A B t g s b y => @lem5092505 A B x f a t g s b y h0 h1 h2)). Qed.
Lemma lem5092508 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) (h2 : term626 A B a b t s f g y) : False.
Proof. exact (or_elim (@lem5082042 A B a b t s f g y h2) (fun h0 : term605 A B a t g s b y => @lem5092507 A B x f a t g s b y h1 h0) (fun h0 : term621 A B a b t s f g y => @lem5092504 A B x a b t s f g y h0 h1)). Qed.
Lemma lem5092509 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term554 A B a s t g f x) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (or_elim (@lem5082073 A B a s t g f x h1) (fun h0 : term1366 A B f x t => @lem5092491 A B x a b t s f g y h0 h1 h2) (fun h0 : term1376 A B g f x => @lem5092489 A B x a b t s f g y h0 h1 h2)). Qed.
Lemma lem5092510 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (s : A -> Prop) (b : B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term526 A B s b t a x) : False.
Proof. exact (or_elim (@lem5082067 A B s b t a x h2) (fun h0 : term1365 B b t => @lem5092495 A B x a b t s f g y h0 h1) (fun h0 : term506 A a x => @lem5092493 A B s b t a x h0 h2)). Qed.
Lemma lem5092511 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term561 A B b a s t g f x) (h2 : term1177 A B x a b t s f g y) : False.
Proof. exact (or_elim (@lem5082061 A B b a s t g f x h1) (fun h0 : term526 A B s b t a x => @lem5092510 A B f g y s b t a x h2 h0) (fun h0 : term554 A B a s t g f x => @lem5092509 A B x a b t s f g y h0 h2)). Qed.
Lemma lem5092512 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term535 A B s f t a x) (h2 : term1177 A B x a b t s f g y) (h3 : term545 A B b s f t a x) : False.
Proof. exact (or_elim (@lem5082057 A B s f t a x h1) (fun h0 : term1366 A B f x t => @lem5092497 A B g y b s f t a x h0 h2 h3) (fun h0 : term506 A a x => @lem5092408 A B g y b s f t a x h1 h2 h3)). Qed.
Lemma lem5092513 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term526 A B s b t a x) (h3 : term545 A B b s f t a x) : False.
Proof. exact (or_elim (@lem5082051 A B s b t a x h2) (fun h0 : term1365 B b t => @lem5092501 A B g y b s f t a x h0 h1 h2 h3) (fun h0 : term506 A a x => @lem5092499 A B s b t a x h0 h2)). Qed.
Lemma lem5092514 {A B : Type'} (g : B -> A) (y : B) (b : B) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (a : A) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term545 A B b s f t a x) : False.
Proof. exact (or_elim (@lem5082045 A B b s f t a x h2) (fun h0 : term526 A B s b t a x => @lem5092513 A B g y b s f t a x h1 h0 h2) (fun h0 : term535 A B s f t a x => @lem5092512 A B g y b s f t a x h0 h1 h2)). Qed.
Lemma lem5092515 {A B : Type'} (y : B) (b : B) (a : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term1177 A B x a b t s f g y) (h2 : term566 A B b a s t g f x) : False.
Proof. exact (or_elim (@lem5082041 A B b a s t g f x h2) (fun h0 : term545 A B b s f t a x => @lem5092514 A B g y b s f t a x h1 h0) (fun h0 : term561 A B b a s t g f x => @lem5092511 A B x a b t s f g y h0 h1)). Qed.
Lemma lem5092516 {A B : Type'} (x : A) (a : A) (b : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term1177 A B x a b t s f g y) : False.
Proof. exact (or_elim (@lem5082039 A B x a b t s f g y h1) (fun h0 : term566 A B b a s t g f x => @lem5092515 A B y b a s t g f x h1 h0) (fun h0 : term626 A B a b t s f g y => @lem5092508 A B x a b t s f g y h1 h0)). Qed.
Lemma lem5092517 {A B : Type'} (x : A) (y : B) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1351 A B x y t b s a f g) : False.
Proof. exact (or_elim (@lem5082022 A B x y t b s a f g h1) (fun h0 : term1177 A B x a b t s f g y => @lem5092516 A B x a b t s f g y h0) (fun h0 : term1238 A B t b s a f g => @lem5092389 A B t b s a f g h0)). Qed.
Lemma lem5092518 {A B : Type'} (x : A) (y : B) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1351 A B x y t b s a f g) : (term1351 A B x y t b s a f g) = False.
Proof. exact (prop_ext (fun h2 : term1351 A B x y t b s a f g => @lem5092517 A B x y t b s a f g h1) (fun h2 : False => @lem5082022 A B x y t b s a f g h1)). Qed.
Lemma lem5092519 {A B : Type'} (x : A) (y : B) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1351 A B x y t b s a f g) : False.
Proof. exact (EQ_MP (@lem5092518 A B x y t b s a f g h1) (@lem5082022 A B x y t b s a f g h1)). Qed.
Lemma lem5092520 {A B : Type'} (x : A) (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1354 A B x t b s a f g) : False.
Proof. exact (ex_elim (@lem5081349 A B x t b s a f g h1) (fun y : B => fun h0 : term1353 A B x t b s a f g y => @lem5092519 A B x y t b s a f g h0)). Qed.
Lemma lem5092521 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1356 A B t b s a f g) : False.
Proof. exact (ex_elim (@lem5081348 A B t b s a f g h1) (fun x : A => fun h0 : term1355 A B t b s a f g x => @lem5092520 A B x t b s a f g h0)). Qed.
Lemma lem5092522 {A B : Type'} (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term1358 A B b s a f g) : False.
Proof. exact (ex_elim (@lem5081347 A B b s a f g h1) (fun t : B -> Prop => fun h0 : term1357 A B b s a f g t => @lem5092521 A B t b s a f g h0)). Qed.
Lemma lem5092523 {A B : Type'} (b : B) (a : A) (f : A -> B) (g : B -> A) (h1 : term1360 A B b a f g) : False.
Proof. exact (ex_elim (@lem5081346 A B b a f g h1) (fun s : A -> Prop => fun h0 : term1359 A B b a f g s => @lem5092522 A B b s a f g h0)). Qed.
Lemma lem5092524 {A B : Type'} (b : B) (a : A) (g : B -> A) (h1 : term1362 A B b a g) : False.
Proof. exact (ex_elim (@lem5081345 A B b a g h1) (fun f : A -> B => fun h0 : term1361 A B b a g f => @lem5092523 A B b a f g h0)). Qed.
Lemma lem5092525 {A B : Type'} (a : A) (g : B -> A) (h1 : term499 A B a g) : False.
Proof. exact (ex_elim (@lem5081344 A B a g h1) (fun b : B => fun h0 : term1363 A B a g b => @lem5092524 A B b a g h0)). Qed.
Lemma lem5092526 {A B : Type'} (a : A) (g : B -> A) (h1 : term499 A B a g) : (term499 A B a g) = False.
Proof. exact (prop_ext (fun h2 : term499 A B a g => @lem5092525 A B a g h1) (fun h2 : False => @lem5079194 A B a g h1)). Qed.
Lemma lem5092527 {A B : Type'} (a : A) (g : B -> A) (h1 : term499 A B a g) : False.
Proof. exact (EQ_MP (@lem5092526 A B a g h1) (@lem5079194 A B a g h1)). Qed.
Lemma lem5092528 {A B : Type'} (a : A) (g : B -> A) : term498 A B a g.
Proof. exact (fun h0 : term499 A B a g => @lem5092527 A B a g h0). Qed.
Lemma lem5092529 {A B : Type'} (a : A) (g : B -> A) : term492 A B a g.
Proof. exact (EQ_MP (@lem5079193 A B a g) (@lem5092528 A B a g)). Qed.
Lemma lem5092534 {A B : Type'} (g : B -> A) : term495 A B g.
Proof. exact (fun a : A => @lem5092529 A B a g). Qed.
Lemma lem5092539 {A B : Type'} : term497 A B.
Proof. exact (fun g : B -> A => @lem5092534 A B g). Qed.
Lemma lem5092540 {A B : Type'} : term239 A B.
Proof. exact (EQ_MP (@lem5079189 A B) (@lem5092539 A B)). Qed.
Lemma lem5092541 {A B : Type'} (g : B -> A) : term1547 A B g.
Proof. exact (@lem5092540 A B g). Qed.
Lemma lem5092542 {A B : Type'} (g : B -> A) : (term1547 A B g) = (term235 A B g).
Proof. exact (eq_refl (term1547 A B g)). Qed.
Lemma lem5092543 {A B : Type'} (g : B -> A) : term235 A B g.
Proof. exact (EQ_MP (@lem5092542 A B g) (@lem5092541 A B g)). Qed.
Lemma lem5092544 {A B : Type'} (g : B -> A) (a : A) : term1548 A B g a.
Proof. exact (@lem5092543 A B g a). Qed.
Lemma lem5092545 {A B : Type'} (a : A) (g : B -> A) : (term1548 A B g a) = (term231 A B a g).
Proof. exact (eq_refl (term1548 A B g a)). Qed.
Lemma lem5092546 {A B : Type'} (a : A) (g : B -> A) : term231 A B a g.
Proof. exact (EQ_MP (@lem5092545 A B a g) (@lem5092544 A B g a)). Qed.
Lemma lem5092547 {A B : Type'} (a : A) (g : B -> A) (b : B) : term1549 A B a g b.
Proof. exact (@lem5092546 A B a g b). Qed.
Lemma lem5092548 {A B : Type'} (b : B) (a : A) (g : B -> A) : (term1549 A B a g b) = (term227 A B b a g).
Proof. exact (eq_refl (term1549 A B a g b)). Qed.
Lemma lem5092549 {A B : Type'} (b : B) (a : A) (g : B -> A) : term227 A B b a g.
Proof. exact (EQ_MP (@lem5092548 A B b a g) (@lem5092547 A B a g b)). Qed.
Lemma lem5092550 {A B : Type'} (b : B) (a : A) (g : B -> A) (f : A -> B) : term1550 A B b a g f.
Proof. exact (@lem5092549 A B b a g f). Qed.
Lemma lem5092551 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) : (term1550 A B b a g f) = (term223 A B f b a g).
Proof. exact (eq_refl (term1550 A B b a g f)). Qed.
Lemma lem5092552 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) : term223 A B f b a g.
Proof. exact (EQ_MP (@lem5092551 A B f b a g) (@lem5092550 A B b a g f)). Qed.
Lemma lem5092553 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (s : A -> Prop) : term1551 A B f b a g s.
Proof. exact (@lem5092552 A B f b a g s). Qed.
Lemma lem5092554 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term1551 A B f b a g s) = (term219 A B s f b a g).
Proof. exact (eq_refl (term1551 A B f b a g s)). Qed.
Lemma lem5092555 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : term219 A B s f b a g.
Proof. exact (EQ_MP (@lem5092554 A B s f b a g) (@lem5092553 A B f b a g s)). Qed.
Lemma lem5092556 {A B : Type'} (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (t : B -> Prop) : term1552 A B s f b a g t.
Proof. exact (@lem5092555 A B s f b a g t). Qed.
Lemma lem5092557 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : (term1552 A B s f b a g t) = (term193 A B t s f b a g).
Proof. exact (eq_refl (term1552 A B s f b a g t)). Qed.
Lemma lem5092558 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : term193 A B t s f b a g.
Proof. exact (EQ_MP (@lem5092557 A B t s f b a g) (@lem5092556 A B s f b a g t)). Qed.
Lemma lem5092560 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) : term193 A B t s f b a g.
Proof. exact (@lem5077284 A B t s f b a g (@lem5092558 A B t s f b a g)). Qed.
Lemma lem5092561 {A B : Type'} (t : B -> Prop) (f : A -> B) (b : B) (a : A) (g : B -> A) (s : A -> Prop) (h1 : @FINITE A s) : term214 A B t s f b a g.
Proof. exact (@lem5092560 A B t s f b a g (@lem5073237 A s h1)). Qed.
Lemma lem5092562 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term211 A B t s f b a g.
Proof. exact (@lem5092561 A B t f b a g s h1 (@lem5073239 B t h2)). Qed.
Lemma lem5092563 {A B : Type'} (f : A -> B) (b : B) (a : A) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) : term208 A B t s f b a g.
Proof. exact (@lem5092562 A B f b a g s t h1 h2 (@lem5073241 A B s t h3)). Qed.
Lemma lem5092564 {A B : Type'} (f : A -> B) (b : B) (g : B -> A) (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) : term206 A B t s f b a g.
Proof. exact (@lem5092563 A B f b a g s t h1 h2 h3 (@lem5073243 A a s h4)). Qed.
Lemma lem5092565 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term203 A B t s f b a g.
Proof. exact (@lem5092564 A B f b g t a s h1 h2 h3 h4 (@lem5073242 B b t h5)). Qed.
Lemma lem5092566 {A B : Type'} (g : B -> A) (f : A -> B) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : @IN A a s) (h6 : @IN B b t) : term200 A B t s f b a g.
Proof. exact (@lem5092565 A B f g a s b t h2 h3 h4 h5 h6 (@lem5077263 A B s a t b g f h1)). Qed.
Lemma lem5092567 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term191 A B t s f b a g.
Proof. exact (@lem5092566 A B g f a s b t h1 h3 h4 h5 h6 h7 (@lem5077262 A B t b s a f g h2)). Qed.
Lemma lem5092568 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : term192 A B t s f b a g) (h6 : (@CARD A s) = (@CARD B t)) (h7 : @IN A a s) (h8 : @IN B b t) : False.
Proof. exact (@lem5092567 A B f g a s b t h1 h2 h3 h4 h6 h7 h8 (@lem5077268 A B t s f b a g h5)). Qed.
Lemma lem5092569 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : term192 A B t s f b a g) (h6 : (@CARD A s) = (@CARD B t)) (h7 : @IN A a s) (h8 : @IN B b t) : (term192 A B t s f b a g) = False.
Proof. exact (prop_ext (fun h9 : term192 A B t s f b a g => @lem5092568 A B f g a s b t h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5077268 A B t s f b a g h5)). Qed.
Lemma lem5092570 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : term192 A B t s f b a g) (h6 : (@CARD A s) = (@CARD B t)) (h7 : @IN A a s) (h8 : @IN B b t) : False.
Proof. exact (EQ_MP (@lem5092569 A B f g a s b t h1 h2 h3 h4 h5 h6 h7 h8) (@lem5077268 A B t s f b a g h5)). Qed.
Lemma lem5092571 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term191 A B t s f b a g.
Proof. exact (fun h0 : term192 A B t s f b a g => @lem5092570 A B f g a s b t h1 h2 h3 h4 h0 h5 h6 h7). Qed.
Lemma lem5092572 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term190 A B t s f b a g.
Proof. exact (EQ_MP (@lem5077267 A B t s f b a g) (@lem5092571 A B f g a s b t h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5092573 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term1553 A B t s a b f.
Proof. exact (ex_intro (term1554 A B t s a b f) (term1555 A B b a g) (@lem5092572 A B f g a s b t h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5092574 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term42 A B b a t s.
Proof. exact (ex_intro (term1556 A B b a t s) (term1557 A B a b f) (@lem5092573 A B f g a s b t h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5092575 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term135 A B t b s a f g) : term133 A B t b s a f g.
Proof. exact (proj2 (@lem5077261 A B t b s a f g h1)). Qed.
Lemma lem5092576 {A B : Type'} (t : B -> Prop) (b : B) (s : A -> Prop) (a : A) (f : A -> B) (g : B -> A) (h1 : term135 A B t b s a f g) : term109 A B s a t b g f.
Proof. exact (proj1 (@lem5077261 A B t b s a f g h1)). Qed.
Lemma lem5092577 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : (term133 A B t b s a f g) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h8 : term133 A B t b s a f g => @lem5092574 A B f g a s b t h1 h2 h3 h4 h5 h6 h7) (fun h8 : term42 A B b a t s => @lem5077262 A B t b s a f g h2)). Qed.
Lemma lem5092578 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092577 A B f g a s b t h1 h2 h3 h4 h5 h6 h7) (@lem5077262 A B t b s a f g h2)). Qed.
Lemma lem5092579 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : (term109 A B s a t b g f) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h8 : term109 A B s a t b g f => @lem5092578 A B f g a s b t h1 h2 h3 h4 h5 h6 h7) (fun h8 : term42 A B b a t s => @lem5077263 A B s a t b g f h1)). Qed.
Lemma lem5092580 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : term133 A B t b s a f g) (h3 : @FINITE A s) (h4 : @FINITE B t) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092579 A B f g a s b t h1 h2 h3 h4 h5 h6 h7) (@lem5077263 A B s a t b g f h1)). Qed.
Lemma lem5092581 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term135 A B t b s a f g) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : (term133 A B t b s a f g) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h8 : term133 A B t b s a f g => @lem5092580 A B f g a s b t h1 h8 h2 h3 h5 h6 h7) (fun h8 : term42 A B b a t s => @lem5092575 A B t b s a f g h4)). Qed.
Lemma lem5092582 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term109 A B s a t b g f) (h2 : @FINITE A s) (h3 : @FINITE B t) (h4 : term135 A B t b s a f g) (h5 : (@CARD A s) = (@CARD B t)) (h6 : @IN A a s) (h7 : @IN B b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092581 A B f g a s b t h1 h2 h3 h4 h5 h6 h7) (@lem5092575 A B t b s a f g h4)). Qed.
Lemma lem5092583 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term135 A B t b s a f g) (h4 : (@CARD A s) = (@CARD B t)) (h5 : @IN A a s) (h6 : @IN B b t) : (term109 A B s a t b g f) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h7 : term109 A B s a t b g f => @lem5092582 A B f g a s b t h7 h1 h2 h3 h4 h5 h6) (fun h7 : term42 A B b a t s => @lem5092576 A B t b s a f g h3)). Qed.
Lemma lem5092584 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term135 A B t b s a f g) (h4 : (@CARD A s) = (@CARD B t)) (h5 : @IN A a s) (h6 : @IN B b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092583 A B f g a s b t h1 h2 h3 h4 h5 h6) (@lem5092576 A B t b s a f g h3)). Qed.
Lemma lem5092585 {A B : Type'} (f : A -> B) (g : B -> A) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term183 A B f g b a t s.
Proof. exact (fun h0 : term135 A B t b s a f g => @lem5092584 A B f g a s b t h1 h2 h0 h3 h4 h5). Qed.
Lemma lem5092590 {A B : Type'} (f : A -> B) (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term186 A B f b a t s.
Proof. exact (fun g : B -> A => @lem5092585 A B f g a s b t h1 h2 h3 h4 h5). Qed.
Lemma lem5092595 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term188 A B b a t s.
Proof. exact (fun f : A -> B => @lem5092590 A B f a s b t h1 h2 h3 h4 h5). Qed.
Lemma lem5092596 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term150 A B b a t s.
Proof. exact (EQ_MP (@lem5077260 A B a s b t h1 h2 h3 h4 h5) (@lem5092595 A B a s b t h1 h2 h3 h4 h5)). Qed.
Lemma lem5092597 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term42 A B b a t s.
Proof. exact (@lem5092596 A B a s b t h1 h2 h3 h4 h5 (@lem5073234 A B t b s a)). Qed.
Lemma lem5092598 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term12 A B a s b t) : term13 A B a s b t.
Proof. exact (proj2 (@lem5073235 A B a s b t h1)). Qed.
Lemma lem5092599 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term12 A B a s b t) : @FINITE A s.
Proof. exact (proj1 (@lem5073235 A B a s b t h1)). Qed.
Lemma lem5092600 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term13 A B a s b t) : term14 A B a s b t.
Proof. exact (proj2 (@lem5073236 A B a s b t h1)). Qed.
Lemma lem5092601 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term13 A B a s b t) : @FINITE B t.
Proof. exact (proj1 (@lem5073236 A B a s b t h1)). Qed.
Lemma lem5092602 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term14 A B a s b t) : term15 A B a s b t.
Proof. exact (proj2 (@lem5073238 A B a s b t h1)). Qed.
Lemma lem5092603 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term14 A B a s b t) : (@CARD A s) = (@CARD B t).
Proof. exact (proj1 (@lem5073238 A B a s b t h1)). Qed.
Lemma lem5092604 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term15 A B a s b t) : @IN B b t.
Proof. exact (proj2 (@lem5073240 A B a s b t h1)). Qed.
Lemma lem5092605 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term15 A B a s b t) : @IN A a s.
Proof. exact (proj1 (@lem5073240 A B a s b t h1)). Qed.
Lemma lem5092606 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (@IN B b t) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h6 : @IN B b t => @lem5092597 A B a s b t h1 h2 h3 h4 h5) (fun h6 : term42 A B b a t s => @lem5073242 B b t h5)). Qed.
Lemma lem5092607 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092606 A B a s b t h1 h2 h3 h4 h5) (@lem5073242 B b t h5)). Qed.
Lemma lem5092608 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : (@IN A a s) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h6 : @IN A a s => @lem5092607 A B a s b t h1 h2 h3 h4 h5) (fun h6 : term42 A B b a t s => @lem5073243 A a s h4)). Qed.
Lemma lem5092609 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : (@CARD A s) = (@CARD B t)) (h4 : @IN A a s) (h5 : @IN B b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092608 A B a s b t h1 h2 h3 h4 h5) (@lem5073243 A a s h4)). Qed.
Lemma lem5092610 {A B : Type'} (b : B) (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term15 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : @IN A a s) : (@IN B b t) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h6 : @IN B b t => @lem5092609 A B a s b t h1 h2 h4 h5 h6) (fun h6 : term42 A B b a t s => @lem5092604 A B a s b t h3)). Qed.
Lemma lem5092611 {A B : Type'} (b : B) (t : B -> Prop) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term15 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) (h5 : @IN A a s) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092610 A B b t a s h1 h2 h3 h4 h5) (@lem5092604 A B a s b t h3)). Qed.
Lemma lem5092612 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term15 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) : (@IN A a s) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h5 : @IN A a s => @lem5092611 A B b t a s h1 h2 h3 h4 h5) (fun h5 : term42 A B b a t s => @lem5092605 A B a s b t h3)). Qed.
Lemma lem5092613 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term15 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092612 A B a b s t h1 h2 h3 h4) (@lem5092605 A B a s b t h3)). Qed.
Lemma lem5092614 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term15 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) : ((@CARD A s) = (@CARD B t)) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h5 : (@CARD A s) = (@CARD B t) => @lem5092613 A B a b s t h1 h2 h3 h4) (fun h5 : term42 A B b a t s => @lem5073241 A B s t h4)). Qed.
Lemma lem5092615 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term15 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092614 A B a b s t h1 h2 h3 h4) (@lem5073241 A B s t h4)). Qed.
Lemma lem5092616 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term14 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) : (term15 A B a s b t) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h5 : term15 A B a s b t => @lem5092615 A B a b s t h1 h2 h5 h4) (fun h5 : term42 A B b a t s => @lem5092602 A B a s b t h3)). Qed.
Lemma lem5092617 {A B : Type'} (a : A) (b : B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term14 A B a s b t) (h4 : (@CARD A s) = (@CARD B t)) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092616 A B a b s t h1 h2 h3 h4) (@lem5092602 A B a s b t h3)). Qed.
Lemma lem5092618 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term14 A B a s b t) : ((@CARD A s) = (@CARD B t)) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h4 : (@CARD A s) = (@CARD B t) => @lem5092617 A B a b s t h1 h2 h3 h4) (fun h4 : term42 A B b a t s => @lem5092603 A B a s b t h3)). Qed.
Lemma lem5092619 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term14 A B a s b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092618 A B a s b t h1 h2 h3) (@lem5092603 A B a s b t h3)). Qed.
Lemma lem5092620 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term14 A B a s b t) : (@FINITE B t) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem5092619 A B a s b t h1 h2 h3) (fun h4 : term42 A B b a t s => @lem5073239 B t h2)). Qed.
Lemma lem5092621 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term14 A B a s b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092620 A B a s b t h1 h2 h3) (@lem5073239 B t h2)). Qed.
Lemma lem5092622 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term13 A B a s b t) : (term14 A B a s b t) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h4 : term14 A B a s b t => @lem5092621 A B a s b t h1 h2 h4) (fun h4 : term42 A B b a t s => @lem5092600 A B a s b t h3)). Qed.
Lemma lem5092623 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) (h3 : term13 A B a s b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092622 A B a s b t h1 h2 h3) (@lem5092600 A B a s b t h3)). Qed.
Lemma lem5092624 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term13 A B a s b t) : (@FINITE B t) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem5092623 A B a s b t h1 h3 h2) (fun h3 : term42 A B b a t s => @lem5092601 A B a s b t h2)). Qed.
Lemma lem5092625 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term13 A B a s b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092624 A B a s b t h1 h2) (@lem5092601 A B a s b t h2)). Qed.
Lemma lem5092626 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term13 A B a s b t) : (@FINITE A s) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem5092625 A B a s b t h1 h2) (fun h3 : term42 A B b a t s => @lem5073237 A s h1)). Qed.
Lemma lem5092627 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term13 A B a s b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092626 A B a s b t h1 h2) (@lem5073237 A s h1)). Qed.
Lemma lem5092628 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term12 A B a s b t) : (term13 A B a s b t) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h3 : term13 A B a s b t => @lem5092627 A B a s b t h1 h3) (fun h3 : term42 A B b a t s => @lem5092598 A B a s b t h2)). Qed.
Lemma lem5092629 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term12 A B a s b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092628 A B a s b t h1 h2) (@lem5092598 A B a s b t h2)). Qed.
Lemma lem5092630 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term12 A B a s b t) : (@FINITE A s) = (term42 A B b a t s).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem5092629 A B a s b t h2 h1) (fun h2 : term42 A B b a t s => @lem5092599 A B a s b t h1)). Qed.
Lemma lem5092631 {A B : Type'} (a : A) (s : A -> Prop) (b : B) (t : B -> Prop) (h1 : term12 A B a s b t) : term42 A B b a t s.
Proof. exact (EQ_MP (@lem5092630 A B a s b t h1) (@lem5092599 A B a s b t h1)). Qed.
Lemma lem5092632 {A B : Type'} (b : B) (a : A) (t : B -> Prop) (s : A -> Prop) : term1558 A B b a t s.
Proof. exact (fun h0 : term12 A B a s b t => @lem5092631 A B a s b t h0). Qed.
Lemma lem5092637 {A B : Type'} (a : A) (t : B -> Prop) (s : A -> Prop) : term1559 A B a t s.
Proof. exact (fun b : B => @lem5092632 A B b a t s). Qed.
Lemma lem5092642 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term1560 A B t s.
Proof. exact (fun a : A => @lem5092637 A B a t s). Qed.
Lemma lem5092647 {A B : Type'} (s : A -> Prop) : term1561 A B s.
Proof. exact (fun t : B -> Prop => @lem5092642 A B t s). Qed.
Lemma lem5092652 {A B : Type'} : term1562 A B.
Proof. exact (fun s : A -> Prop => @lem5092647 A B s). Qed.
