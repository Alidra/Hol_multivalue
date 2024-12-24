Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_LEFT_INVERSE_term_abbrevs.
Require Import INJECTIVE_ON_LEFT_INVERSE_spec.
Require Import IN_UNIV_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem3576207 {A B : Type'} : term0 A B.
Proof. exact (@lem3566182 A B). Qed.
Lemma lem3576208 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem3576207 A B f). Qed.
Lemma lem3576209 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem3576210 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem3576209 A B f) (@lem3576208 A B f)). Qed.
Lemma lem3576211 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem3576210 A B f (@UNIV A)). Qed.
Lemma lem3576212 {A B : Type'} (f : A -> B) : (term3 A B f) = ((term4 A B f) = (term5 A B f)).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem3576213 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A B f).
Proof. exact (EQ_MP (@lem3576212 A B f) (@lem3576211 A B f)). Qed.
Lemma lem3576214 {A : Type'} (x : A) : term6 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem3576215 {A : Type'} (x : A) : (term6 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term6 A x)). Qed.
Lemma lem3576216 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem3576215 A x) (@lem3576214 A x)). Qed.
Lemma lem3576217 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem3576234 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576217 A x) (@lem3576216 A x)). Qed.
Lemma lem3576235 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576234 A x). Qed.
Lemma lem3576236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576237 {A : Type'} (x : A) : (term7 A x) = (and True).
Proof. exact (MK_COMB (@lem3576236) (@lem3576235 A x)). Qed.
Lemma lem3576241 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576217 A x) (@lem3576216 A x)). Qed.
Lemma lem3576242 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576241 A x). Qed.
Lemma lem3576243 {A : Type'} (y : A) : (@IN A y (@UNIV A)) = True.
Proof. exact (@lem3576242 A y). Qed.
Lemma lem3576244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576245 {A : Type'} (y : A) : (term7 A y) = (and True).
Proof. exact (MK_COMB (@lem3576244) (@lem3576243 A y)). Qed.
Lemma lem3576248 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3576249 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term8 A B x f y) = (term9 A B x f y).
Proof. exact (MK_COMB (@lem3576245 A y) (@lem3576248 A B x f y)). Qed.
Lemma lem3576251 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3576252 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term9 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem3576251 ((f x) = (f y))). Qed.
Lemma lem3576255 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term8 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem3576249 A B x f y) (@lem3576252 A B x f y)). Qed.
Lemma lem3576256 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term10 A B x f y) = (term9 A B x f y).
Proof. exact (MK_COMB (@lem3576237 A x) (@lem3576255 A B x f y)). Qed.
Lemma lem3576258 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3576259 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term9 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem3576258 ((f x) = (f y))). Qed.
Lemma lem3576262 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term10 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem3576256 A B x f y) (@lem3576259 A B x f y)). Qed.
Lemma lem3576263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576264 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term11 A B x f y) = (term12 A B x f y).
Proof. exact (MK_COMB (@lem3576263) (@lem3576262 A B x f y)). Qed.
Lemma lem3576267 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3576268 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term13 A B f x y) = (term14 A B f x y).
Proof. exact (MK_COMB (@lem3576264 A B x f y) (@lem3576267 A x y)). Qed.
Lemma lem3576273 {A B : Type'} (f : A -> B) (x : A) : (term15 A B f x) = (term16 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3576268 A B f x y)). Qed.
Lemma lem3576274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3576275 {A B : Type'} (f : A -> B) (x : A) : (term17 A B f x) = (term18 A B f x).
Proof. exact (MK_COMB (@lem3576274 A) (@lem3576273 A B f x)). Qed.
Lemma lem3576280 {A B : Type'} (f : A -> B) : (term19 A B f) = (term20 A B f).
Proof. exact (fun_ext (fun x : A => @lem3576275 A B f x)). Qed.
Lemma lem3576281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3576282 {A B : Type'} (f : A -> B) : (term4 A B f) = (term21 A B f).
Proof. exact (MK_COMB (@lem3576281 A) (@lem3576280 A B f)). Qed.
Lemma lem3576287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3576288 {A B : Type'} (f : A -> B) : (term22 A B f) = (term23 A B f).
Proof. exact (MK_COMB (@lem3576287) (@lem3576282 A B f)). Qed.
Lemma lem3576300 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576217 A x) (@lem3576216 A x)). Qed.
Lemma lem3576301 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576300 A x). Qed.
Lemma lem3576302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576303 {A : Type'} (x : A) : (term24 A x) = (imp True).
Proof. exact (MK_COMB (@lem3576302) (@lem3576301 A x)). Qed.
Lemma lem3576306 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term25 A B g f x) = x) = ((term25 A B g f x) = x).
Proof. exact (eq_refl ((term25 A B g f x) = x)). Qed.
Lemma lem3576307 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term26 A B g f x) = (term27 A B g f x).
Proof. exact (MK_COMB (@lem3576303 A x) (@lem3576306 A B g f x)). Qed.
Lemma lem3576309 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3576310 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term27 A B g f x) = ((term25 A B g f x) = x).
Proof. exact (@lem3576309 ((term25 A B g f x) = x)). Qed.
Lemma lem3576313 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term26 A B g f x) = ((term25 A B g f x) = x).
Proof. exact (TRANS (@lem3576307 A B g f x) (@lem3576310 A B g f x)). Qed.
Lemma lem3576314 {A B : Type'} (g : B -> A) (f : A -> B) : (term28 A B g f) = (term29 A B g f).
Proof. exact (fun_ext (fun x : A => @lem3576313 A B g f x)). Qed.
Lemma lem3576315 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3576316 {A B : Type'} (g : B -> A) (f : A -> B) : (term30 A B g f) = (term31 A B g f).
Proof. exact (MK_COMB (@lem3576315 A) (@lem3576314 A B g f)). Qed.
Lemma lem3576321 {A B : Type'} (f : A -> B) : (term32 A B f) = (term33 A B f).
Proof. exact (fun_ext (fun g : B -> A => @lem3576316 A B g f)). Qed.
Lemma lem3576322 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3576323 {A B : Type'} (f : A -> B) : (term5 A B f) = (term34 A B f).
Proof. exact (MK_COMB (@lem3576322 A B) (@lem3576321 A B f)). Qed.
Lemma lem3576328 {A B : Type'} (f : A -> B) : ((term4 A B f) = (term5 A B f)) = ((term21 A B f) = (term34 A B f)).
Proof. exact (MK_COMB (@lem3576288 A B f) (@lem3576323 A B f)). Qed.
Lemma lem3576335 {A B : Type'} (f : A -> B) : (term21 A B f) = (term34 A B f).
Proof. exact (EQ_MP (@lem3576328 A B f) (@lem3576213 A B f)). Qed.
Lemma lem3576336 {_91597 _91600 : Type'} (f : _91597 -> _91600) : (term21 _91597 _91600 f) = (term34 _91597 _91600 f).
Proof. exact (@lem3576335 _91597 _91600 f). Qed.
Lemma lem3576347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3576348 {_91597 _91600 : Type'} (f : _91597 -> _91600) : (term23 _91597 _91600 f) = (term35 _91597 _91600 f).
Proof. exact (MK_COMB (@lem3576347) (@lem3576336 _91597 _91600 f)). Qed.
Lemma lem3576359 {_91597 _91600 : Type'} (f : _91597 -> _91600) : (term34 _91597 _91600 f) = (term34 _91597 _91600 f).
Proof. exact (eq_refl (term34 _91597 _91600 f)). Qed.
Lemma lem3576360 {_91597 _91600 : Type'} (f : _91597 -> _91600) : ((term21 _91597 _91600 f) = (term34 _91597 _91600 f)) = ((term34 _91597 _91600 f) = (term34 _91597 _91600 f)).
Proof. exact (MK_COMB (@lem3576348 _91597 _91600 f) (@lem3576359 _91597 _91600 f)). Qed.
Lemma lem3576362 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3576363 (x : Prop) : (x = x) = True.
Proof. exact (@lem3576362 Prop x). Qed.
Lemma lem3576364 {_91597 _91600 : Type'} (f : _91597 -> _91600) : ((term34 _91597 _91600 f) = (term34 _91597 _91600 f)) = True.
Proof. exact (@lem3576363 (term34 _91597 _91600 f)). Qed.
Lemma lem3576365 {_91597 _91600 : Type'} (f : _91597 -> _91600) : ((term21 _91597 _91600 f) = (term34 _91597 _91600 f)) = True.
Proof. exact (TRANS (@lem3576360 _91597 _91600 f) (@lem3576364 _91597 _91600 f)). Qed.
Lemma lem3576366 {_91597 _91600 : Type'} (f : _91597 -> _91600) : True = ((term21 _91597 _91600 f) = (term34 _91597 _91600 f)).
Proof. exact (SYM (@lem3576365 _91597 _91600 f)). Qed.
Lemma lem3576367 {_91597 _91600 : Type'} (f : _91597 -> _91600) : (term21 _91597 _91600 f) = (term34 _91597 _91600 f).
Proof. exact (EQ_MP (@lem3576366 _91597 _91600 f) (@lem0)). Qed.
