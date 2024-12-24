Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_EXTENSION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem4387243 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4387244 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem4387245 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem4387244 A B f) (@lem4387243 A B f)). Qed.
Lemma lem4387246 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem4387245 A B f g). Qed.
Lemma lem4387247 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem4387249 {A B : Type'} (s : A -> Prop) : term4 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4387250 {A B : Type'} (s : A -> Prop) : (term4 A B s) = (term5 A B s).
Proof. exact (eq_refl (term4 A B s)). Qed.
Lemma lem4387251 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (EQ_MP (@lem4387250 A B s) (@lem4387249 A B s)). Qed.
Lemma lem4387252 {A B : Type'} (s : A -> Prop) (f : A -> B) : term6 A B s f.
Proof. exact (@lem4387251 A B s f). Qed.
Lemma lem4387253 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term6 A B s f) = (term7 A B s f).
Proof. exact (eq_refl (term6 A B s f)). Qed.
Lemma lem4387254 {A B : Type'} (s : A -> Prop) (f : A -> B) : term7 A B s f.
Proof. exact (EQ_MP (@lem4387253 A B s f) (@lem4387252 A B s f)). Qed.
Lemma lem4387255 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term8 A B s f x.
Proof. exact (@lem4387254 A B s f x). Qed.
Lemma lem4387256 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term8 A B s f x) = ((@RESTRICTION A B s f x) = (term9 A B s f x)).
Proof. exact (eq_refl (term8 A B s f x)). Qed.
Lemma lem4387265 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem4387247 A B f g) (@lem4387246 A B f g)). Qed.
Lemma lem4387266 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (@lem4387265 A B f g). Qed.
Lemma lem4387267 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : ((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term10 A B f s g).
Proof. exact (@lem4387266 A B (@RESTRICTION A B s f) (@RESTRICTION A B s g)). Qed.
Lemma lem4387277 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term9 A B s f x).
Proof. exact (EQ_MP (@lem4387256 A B s f x) (@lem4387255 A B s f x)). Qed.
Lemma lem4387278 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term9 A B s f x).
Proof. exact (@lem4387277 A B s f x). Qed.
Lemma lem4387279 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4387280 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term11 A B s f x) = (term12 A B s f x).
Proof. exact (MK_COMB (@lem4387279 B) (@lem4387278 A B s f x)). Qed.
Lemma lem4387282 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term9 A B s f x).
Proof. exact (EQ_MP (@lem4387256 A B s f x) (@lem4387255 A B s f x)). Qed.
Lemma lem4387283 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term9 A B s f x).
Proof. exact (@lem4387282 A B s f x). Qed.
Lemma lem4387284 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (@RESTRICTION A B s g x) = (term9 A B s g x).
Proof. exact (@lem4387283 A B s g x). Qed.
Lemma lem4387285 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : ((@RESTRICTION A B s f x) = (@RESTRICTION A B s g x)) = ((term9 A B s f x) = (term9 A B s g x)).
Proof. exact (MK_COMB (@lem4387280 A B s f x) (@lem4387284 A B s g x)). Qed.
Lemma lem4387290 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term13 A B f s g) = (term14 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4387285 A B f s g x)). Qed.
Lemma lem4387291 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387292 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term10 A B f s g) = (term15 A B f s g).
Proof. exact (MK_COMB (@lem4387291 A) (@lem4387290 A B f s g)). Qed.
Lemma lem4387297 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : ((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term15 A B f s g).
Proof. exact (TRANS (@lem4387267 A B f s g) (@lem4387292 A B f s g)). Qed.
Lemma lem4387298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4387299 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term16 A B f s g) = (term17 A B f s g).
Proof. exact (MK_COMB (@lem4387298) (@lem4387297 A B f s g)). Qed.
Lemma lem4387310 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term18 A B s f g) = (term18 A B s f g).
Proof. exact (eq_refl (term18 A B s f g)). Qed.
Lemma lem4387311 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term18 A B s f g)) = ((term15 A B f s g) = (term18 A B s f g)).
Proof. exact (MK_COMB (@lem4387299 A B f s g) (@lem4387310 A B s f g)). Qed.
Lemma lem4387316 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term15 A B f s g) = (term18 A B s f g)) = (((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term18 A B s f g)).
Proof. exact (SYM (@lem4387311 A B s f g)). Qed.
Lemma lem4387318 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4387319 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term15 A B f s g) = (term18 A B s f g)) = (term20 A B s f g).
Proof. exact (@lem4387318 ((term15 A B f s g) = (term18 A B s f g))). Qed.
Lemma lem4387320 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term20 A B s f g) = ((term15 A B f s g) = (term18 A B s f g)).
Proof. exact (SYM (@lem4387319 A B s f g)). Qed.
Lemma lem4387321 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term21 A B s f g) : term21 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4387324 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term20 A B s f g) : term20 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4387325 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term22 A B s f g.
Proof. exact (fun h0 : term20 A B s f g => @lem4387324 A B s f g h0). Qed.
Lemma lem4387326 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term22 A B s f g) : term22 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4387327 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term20 A B s f g) : term20 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4387328 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term20 A B s f g) (h2 : term22 A B s f g) : term20 A B s f g.
Proof. exact (@lem4387326 A B s f g h2 (@lem4387327 A B s f g h1)). Qed.
Lemma lem4387329 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term20 A B s f g) : term23 A B s f g.
Proof. exact (fun h0 : term22 A B s f g => @lem4387328 A B s f g h1 h0). Qed.
Lemma lem4387330 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term22 A B s f g) : term22 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4387331 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term20 A B s f g) (h2 : term22 A B s f g) : term20 A B s f g.
Proof. exact (@lem4387329 A B s f g h1 (@lem4387330 A B s f g h2)). Qed.
Lemma lem4387332 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term22 A B s f g) : term22 A B s f g.
Proof. exact (fun h0 : term20 A B s f g => @lem4387331 A B s f g h0 h1). Qed.
Lemma lem4387333 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term24 A B s f g.
Proof. exact (fun h0 : term22 A B s f g => @lem4387332 A B s f g h0). Qed.
Lemma lem4387336 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term22 A B s f g.
Proof. exact (@lem4387333 A B s f g (@lem4387325 A B s f g)). Qed.
Lemma lem4387337 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term22 A B s f g.
Proof. exact (@lem4387336 A B s f g). Qed.
Lemma lem4387351 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4387352 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term20 A B s f g) = (term25 A B s f g).
Proof. exact (@lem4387351 (term21 A B s f g)). Qed.
Lemma lem4387354 (t : Prop) : (term26 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4387355 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term25 A B s f g) = ((term15 A B f s g) = (term18 A B s f g)).
Proof. exact (@lem4387354 ((term15 A B f s g) = (term18 A B s f g))). Qed.
Lemma lem4387356 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term20 A B s f g) = ((term15 A B f s g) = (term18 A B s f g)).
Proof. exact (TRANS (@lem4387352 A B s f g) (@lem4387355 A B s f g)). Qed.
Lemma lem4387367 {A B : Type'} (f : A -> B) (g : A -> B) : (term27 A B f g) = (term28 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4387356 A B s f g)). Qed.
Lemma lem4387368 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4387369 {A B : Type'} (f : A -> B) (g : A -> B) : (term29 A B f g) = (term30 A B f g).
Proof. exact (MK_COMB (@lem4387368 A) (@lem4387367 A B f g)). Qed.
Lemma lem4387374 {A B : Type'} (g : A -> B) : (term31 A B g) = (term32 A B g).
Proof. exact (fun_ext (fun f : A -> B => @lem4387369 A B f g)). Qed.
Lemma lem4387375 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4387376 {A B : Type'} (g : A -> B) : (term33 A B g) = (term34 A B g).
Proof. exact (MK_COMB (@lem4387375 A B) (@lem4387374 A B g)). Qed.
Lemma lem4387381 {A B : Type'} : (term35 A B) = (term36 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem4387376 A B g)). Qed.
Lemma lem4387382 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4387391 {A B : Type'} : (term37 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem4387382 A B) (@lem4387381 A B)). Qed.
Lemma lem4387396 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term39 A B s f g x) = (term39 A B s f g x).
Proof. exact (eq_refl (term39 A B s f g x)). Qed.
Lemma lem4387397 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term40 A B s f g) = (term40 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387396 A B s f g x)). Qed.
Lemma lem4387398 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387399 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term18 A B s f g) = (term18 A B s f g).
Proof. exact (MK_COMB (@lem4387398 A) (@lem4387397 A B s f g)). Qed.
Lemma lem4387403 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem4387404 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4387405 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term41 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem4387404 B) (@lem4387403 A x s h1)). Qed.
Lemma lem4387406 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4387407 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term42 A B s f x) = (term43 A B f x).
Proof. exact (MK_COMB (@lem4387405 A B x s h1) (@lem4387406 A B f x)). Qed.
Lemma lem4387408 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4387409 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term9 A B s f x) = (term44 A B f x).
Proof. exact (MK_COMB (@lem4387407 A B f x s h1) (@lem4387408 B)). Qed.
Lemma lem4387411 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4387412 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4387411 B t1 t2). Qed.
Lemma lem4387413 {A B : Type'} (f : A -> B) (x : A) : (term44 A B f x) = (@ARB B).
Proof. exact (@lem4387412 B (f x) (@ARB B)). Qed.
Lemma lem4387414 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term9 A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4387409 A B f x s h1) (@lem4387413 A B f x)). Qed.
Lemma lem4387415 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4387416 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term12 A B s f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4387415 B) (@lem4387414 A B f x s h1)). Qed.
Lemma lem4387418 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem4387419 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4387420 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term41 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem4387419 B) (@lem4387418 A x s h1)). Qed.
Lemma lem4387421 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4387422 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term42 A B s g x) = (term43 A B g x).
Proof. exact (MK_COMB (@lem4387420 A B x s h1) (@lem4387421 A B g x)). Qed.
Lemma lem4387423 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4387424 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term9 A B s g x) = (term44 A B g x).
Proof. exact (MK_COMB (@lem4387422 A B g x s h1) (@lem4387423 B)). Qed.
Lemma lem4387426 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4387427 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4387426 B t1 t2). Qed.
Lemma lem4387428 {A B : Type'} (g : A -> B) (x : A) : (term44 A B g x) = (@ARB B).
Proof. exact (@lem4387427 B (g x) (@ARB B)). Qed.
Lemma lem4387429 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term9 A B s g x) = (@ARB B).
Proof. exact (TRANS (@lem4387424 A B g x s h1) (@lem4387428 A B g x)). Qed.
Lemma lem4387430 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term9 A B s f x) = (term9 A B s g x)) = ((@ARB B) = (@ARB B)).
Proof. exact (MK_COMB (@lem4387416 A B f x s h1) (@lem4387429 A B g x s h1)). Qed.
Lemma lem4387432 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4387433 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4387432 B x). Qed.
Lemma lem4387434 {B : Type'} : ((@ARB B) = (@ARB B)) = True.
Proof. exact (@lem4387433 B (@ARB B)). Qed.
Lemma lem4387435 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term9 A B s f x) = (term9 A B s g x)) = True.
Proof. exact (TRANS (@lem4387430 A B f g x s h1) (@lem4387434 B)). Qed.
Lemma lem4387436 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : term45 A B f s g x.
Proof. exact (fun h0 : (@IN A x s) = False => @lem4387435 A B f g x s h0). Qed.
Lemma lem4387438 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem4387439 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4387440 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term41 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem4387439 B) (@lem4387438 A x s h1)). Qed.
Lemma lem4387441 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4387442 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term42 A B s f x) = (term46 A B f x).
Proof. exact (MK_COMB (@lem4387440 A B x s h1) (@lem4387441 A B f x)). Qed.
Lemma lem4387443 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4387444 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term9 A B s f x) = (term47 A B f x).
Proof. exact (MK_COMB (@lem4387442 A B f x s h1) (@lem4387443 B)). Qed.
Lemma lem4387446 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4387447 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4387446 B t2 t1). Qed.
Lemma lem4387448 {A B : Type'} (f : A -> B) (x : A) : (term47 A B f x) = (f x).
Proof. exact (@lem4387447 B (@ARB B) (f x)). Qed.
Lemma lem4387449 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term9 A B s f x) = (f x).
Proof. exact (TRANS (@lem4387444 A B f x s h1) (@lem4387448 A B f x)). Qed.
Lemma lem4387450 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4387451 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term12 A B s f x) = (term48 A B f x).
Proof. exact (MK_COMB (@lem4387450 B) (@lem4387449 A B f x s h1)). Qed.
Lemma lem4387453 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem4387454 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4387455 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term41 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem4387454 B) (@lem4387453 A x s h1)). Qed.
Lemma lem4387456 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4387457 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term42 A B s g x) = (term46 A B g x).
Proof. exact (MK_COMB (@lem4387455 A B x s h1) (@lem4387456 A B g x)). Qed.
Lemma lem4387458 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4387459 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term9 A B s g x) = (term47 A B g x).
Proof. exact (MK_COMB (@lem4387457 A B g x s h1) (@lem4387458 B)). Qed.
Lemma lem4387461 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4387462 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4387461 B t2 t1). Qed.
Lemma lem4387463 {A B : Type'} (g : A -> B) (x : A) : (term47 A B g x) = (g x).
Proof. exact (@lem4387462 B (@ARB B) (g x)). Qed.
Lemma lem4387464 {A B : Type'} (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term9 A B s g x) = (g x).
Proof. exact (TRANS (@lem4387459 A B g x s h1) (@lem4387463 A B g x)). Qed.
Lemma lem4387465 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term9 A B s f x) = (term9 A B s g x)) = ((f x) = (g x)).
Proof. exact (MK_COMB (@lem4387451 A B f x s h1) (@lem4387464 A B g x s h1)). Qed.
Lemma lem4387468 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term49 A B s f g x.
Proof. exact (fun h0 : (@IN A x s) = True => @lem4387465 A B f g x s h0). Qed.
Lemma lem4387469 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term50 A B s f g x.
Proof. exact (conj (@lem4387436 A B f s g x) (@lem4387468 A B s f g x)). Qed.
Lemma lem4387471 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term51 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4387472 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) : term52 A B f g x s.
Proof. exact (@lem4387471 ((term9 A B s f x) = (term9 A B s g x)) ((f x) = (g x)) (@IN A x s) True). Qed.
Lemma lem4387473 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) : ((term9 A B s f x) = (term9 A B s g x)) = (term53 A B f g x s).
Proof. exact (@lem4387472 A B f g x s (@lem4387469 A B s f g x)). Qed.
Lemma lem4387475 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4387476 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = True.
Proof. exact (@lem4387475 (@IN A x s)). Qed.
Lemma lem4387481 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term55 A B s f g x) = (term55 A B s f g x).
Proof. exact (eq_refl (term55 A B s f g x)). Qed.
Lemma lem4387482 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term53 A B f g x s) = (term56 A B s f g x).
Proof. exact (MK_COMB (@lem4387481 A B s f g x) (@lem4387476 A x s)). Qed.
Lemma lem4387484 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4387485 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term56 A B s f g x) = (term57 A B s f g x).
Proof. exact (@lem4387484 (term57 A B s f g x)). Qed.
Lemma lem4387486 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term53 A B f g x s) = (term57 A B s f g x).
Proof. exact (TRANS (@lem4387482 A B s f g x) (@lem4387485 A B s f g x)). Qed.
Lemma lem4387497 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : ((term9 A B s f x) = (term9 A B s g x)) = (term57 A B s f g x).
Proof. exact (TRANS (@lem4387473 A B f g x s) (@lem4387486 A B s f g x)). Qed.
Lemma lem4387498 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term14 A B f s g) = (term58 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387497 A B s f g x)). Qed.
Lemma lem4387499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387500 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term15 A B f s g) = (term59 A B s f g).
Proof. exact (MK_COMB (@lem4387499 A) (@lem4387498 A B s f g)). Qed.
Lemma lem4387501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4387502 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term17 A B f s g) = (term60 A B s f g).
Proof. exact (MK_COMB (@lem4387501) (@lem4387500 A B s f g)). Qed.
Lemma lem4387503 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term15 A B f s g) = (term18 A B s f g)) = ((term59 A B s f g) = (term18 A B s f g)).
Proof. exact (MK_COMB (@lem4387502 A B s f g) (@lem4387399 A B s f g)). Qed.
Lemma lem4387504 {A B : Type'} (f : A -> B) (g : A -> B) : (term28 A B f g) = (term61 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4387503 A B s f g)). Qed.
Lemma lem4387505 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4387506 {A B : Type'} (f : A -> B) (g : A -> B) : (term30 A B f g) = (term62 A B f g).
Proof. exact (MK_COMB (@lem4387505 A) (@lem4387504 A B f g)). Qed.
Lemma lem4387507 {A B : Type'} (g : A -> B) : (term32 A B g) = (term63 A B g).
Proof. exact (fun_ext (fun f : A -> B => @lem4387506 A B f g)). Qed.
Lemma lem4387508 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4387509 {A B : Type'} (g : A -> B) : (term34 A B g) = (term64 A B g).
Proof. exact (MK_COMB (@lem4387508 A B) (@lem4387507 A B g)). Qed.
Lemma lem4387510 {A B : Type'} : (term36 A B) = (term65 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem4387509 A B g)). Qed.
Lemma lem4387511 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4387512 {A B : Type'} : (term38 A B) = (term66 A B).
Proof. exact (MK_COMB (@lem4387511 A B) (@lem4387510 A B)). Qed.
Lemma lem4387549 {A B : Type'} : (term37 A B) = (term66 A B).
Proof. exact (TRANS (@lem4387391 A B) (@lem4387512 A B)). Qed.
Lemma lem4387550 {A B : Type'} : (term66 A B) = (term37 A B).
Proof. exact (SYM (@lem4387549 A B)). Qed.
Lemma lem4387552 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4387553 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term59 A B s f g) = (term18 A B s f g)) = (term67 A B s f g).
Proof. exact (@lem4387552 ((term59 A B s f g) = (term18 A B s f g))). Qed.
Lemma lem4387554 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term67 A B s f g) = ((term59 A B s f g) = (term18 A B s f g)).
Proof. exact (SYM (@lem4387553 A B s f g)). Qed.
Lemma lem4387555 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term68 A B s f g) : term68 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4387559 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem4387560 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term70 A B f g x) = (term70 A B f g x).
Proof. exact (eq_refl (term70 A B f g x)). Qed.
Lemma lem4387562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4387563 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term72 A x s).
Proof. exact (MK_COMB (@lem4387562) (@lem4387559 A x s)). Qed.
Lemma lem4387564 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term73 A B s f g x) = (term74 A B s f g x).
Proof. exact (MK_COMB (@lem4387563 A x s) (@lem4387560 A B f g x)). Qed.
Lemma lem4387565 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term75 A B s f g x) = (term73 A B s f g x).
Proof. exact (@lem17160 (term76 A x s) ((f x) = (g x))). Qed.
Lemma lem4387566 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term75 A B s f g x) = (term74 A B s f g x).
Proof. exact (TRANS (@lem4387565 A B s f g x) (@lem4387564 A B s f g x)). Qed.
Lemma lem4387569 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term57 A B s f g x) = (term57 A B s f g x).
Proof. exact (eq_refl (term57 A B s f g x)). Qed.
Lemma lem4387570 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4387571 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term79 A B s f g) = (term80 A B s f g).
Proof. exact (@lem4387570 A (term58 A B s f g)). Qed.
Lemma lem4387572 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term81 A B s f g x) = (term57 A B s f g x).
Proof. exact (eq_refl (term81 A B s f g x)). Qed.
Lemma lem4387573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4387574 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term82 A B s f g x) = (term75 A B s f g x).
Proof. exact (MK_COMB (@lem4387573) (@lem4387572 A B s f g x)). Qed.
Lemma lem4387575 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term82 A B s f g x) = (term74 A B s f g x).
Proof. exact (TRANS (@lem4387574 A B s f g x) (@lem4387566 A B s f g x)). Qed.
Lemma lem4387576 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term83 A B s f g) = (term84 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387575 A B s f g x)). Qed.
Lemma lem4387577 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387578 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term80 A B s f g) = (term85 A B s f g).
Proof. exact (MK_COMB (@lem4387577 A) (@lem4387576 A B s f g)). Qed.
Lemma lem4387579 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term79 A B s f g) = (term85 A B s f g).
Proof. exact (TRANS (@lem4387571 A B s f g) (@lem4387578 A B s f g)). Qed.
Lemma lem4387580 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term58 A B s f g) = (term58 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387569 A B s f g x)). Qed.
Lemma lem4387581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387582 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term59 A B s f g).
Proof. exact (MK_COMB (@lem4387581 A) (@lem4387580 A B s f g)). Qed.
Lemma lem4387591 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term86 A B s f g x) = (term74 A B s f g x).
Proof. exact (@lem17362 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem4387596 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term39 A B s f g x) = (term57 A B s f g x).
Proof. exact (@lem17265 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem4387597 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4387598 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term87 A B s f g) = (term88 A B s f g).
Proof. exact (@lem4387597 A (term40 A B s f g)). Qed.
Lemma lem4387599 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term89 A B s f g x) = (term39 A B s f g x).
Proof. exact (eq_refl (term89 A B s f g x)). Qed.
Lemma lem4387600 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4387601 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term90 A B s f g x) = (term86 A B s f g x).
Proof. exact (MK_COMB (@lem4387600) (@lem4387599 A B s f g x)). Qed.
Lemma lem4387602 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term90 A B s f g x) = (term74 A B s f g x).
Proof. exact (TRANS (@lem4387601 A B s f g x) (@lem4387591 A B s f g x)). Qed.
Lemma lem4387603 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term91 A B s f g) = (term84 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387602 A B s f g x)). Qed.
Lemma lem4387604 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387605 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term88 A B s f g) = (term85 A B s f g).
Proof. exact (MK_COMB (@lem4387604 A) (@lem4387603 A B s f g)). Qed.
Lemma lem4387606 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term87 A B s f g) = (term85 A B s f g).
Proof. exact (TRANS (@lem4387598 A B s f g) (@lem4387605 A B s f g)). Qed.
Lemma lem4387607 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term40 A B s f g) = (term58 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387596 A B s f g x)). Qed.
Lemma lem4387608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387609 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term18 A B s f g) = (term59 A B s f g).
Proof. exact (MK_COMB (@lem4387608 A) (@lem4387607 A B s f g)). Qed.
Lemma lem4387610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4387611 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term92 A B s f g) = (term93 A B s f g).
Proof. exact (MK_COMB (@lem4387610) (@lem4387579 A B s f g)). Qed.
Lemma lem4387612 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term94 A B s f g) = (term95 A B s f g).
Proof. exact (MK_COMB (@lem4387611 A B s f g) (@lem4387609 A B s f g)). Qed.
Lemma lem4387613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4387614 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term96 A B s f g) = (term96 A B s f g).
Proof. exact (MK_COMB (@lem4387613) (@lem4387582 A B s f g)). Qed.
Lemma lem4387615 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term97 A B s f g) = (term98 A B s f g).
Proof. exact (MK_COMB (@lem4387614 A B s f g) (@lem4387606 A B s f g)). Qed.
Lemma lem4387616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4387617 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term99 A B s f g) = (term100 A B s f g).
Proof. exact (MK_COMB (@lem4387616) (@lem4387615 A B s f g)). Qed.
Lemma lem4387618 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term101 A B s f g) = (term102 A B s f g).
Proof. exact (MK_COMB (@lem4387617 A B s f g) (@lem4387612 A B s f g)). Qed.
Lemma lem4387619 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term68 A B s f g) = (term101 A B s f g).
Proof. exact (@lem17646 (term59 A B s f g) (term18 A B s f g)). Qed.
Lemma lem4387620 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term68 A B s f g) = (term102 A B s f g).
Proof. exact (TRANS (@lem4387619 A B s f g) (@lem4387618 A B s f g)). Qed.
Lemma lem4387815 {A : Type'} (P : Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4387816 {A : Type'} (P : Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (@lem4387815 A P Q). Qed.
Lemma lem4387817 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term105 A B s f g) = (term106 A B s f g).
Proof. exact (@lem4387816 A (term59 A B s f g) (term84 A B s f g)). Qed.
Lemma lem4387818 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term107 A B s f g x) = (term74 A B s f g x).
Proof. exact (eq_refl (term107 A B s f g x)). Qed.
Lemma lem4387819 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term108 A B s f g) = (term84 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387818 A B s f g x)). Qed.
Lemma lem4387820 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387821 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term109 A B s f g) = (term85 A B s f g).
Proof. exact (MK_COMB (@lem4387820 A) (@lem4387819 A B s f g)). Qed.
Lemma lem4387822 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term96 A B s f g) = (term96 A B s f g).
Proof. exact (eq_refl (term96 A B s f g)). Qed.
Lemma lem4387823 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term105 A B s f g) = (term98 A B s f g).
Proof. exact (MK_COMB (@lem4387822 A B s f g) (@lem4387821 A B s f g)). Qed.
Lemma lem4387824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4387825 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term110 A B s f g) = (term111 A B s f g).
Proof. exact (MK_COMB (@lem4387824) (@lem4387823 A B s f g)). Qed.
Lemma lem4387826 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term107 A B s f g x) = (term74 A B s f g x).
Proof. exact (eq_refl (term107 A B s f g x)). Qed.
Lemma lem4387827 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term96 A B s f g) = (term96 A B s f g).
Proof. exact (eq_refl (term96 A B s f g)). Qed.
Lemma lem4387828 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term112 A B s f g x) = (term113 A B s f g x).
Proof. exact (MK_COMB (@lem4387827 A B s f g) (@lem4387826 A B s f g x)). Qed.
Lemma lem4387829 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term114 A B s f g) = (term115 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387828 A B s f g x)). Qed.
Lemma lem4387830 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387831 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term106 A B s f g) = (term116 A B s f g).
Proof. exact (MK_COMB (@lem4387830 A) (@lem4387829 A B s f g)). Qed.
Lemma lem4387832 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term105 A B s f g) = (term106 A B s f g)) = ((term98 A B s f g) = (term116 A B s f g)).
Proof. exact (MK_COMB (@lem4387825 A B s f g) (@lem4387831 A B s f g)). Qed.
Lemma lem4387833 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term98 A B s f g) = (term116 A B s f g).
Proof. exact (EQ_MP (@lem4387832 A B s f g) (@lem4387817 A B s f g)). Qed.
Lemma lem4387834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4387835 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term100 A B s f g) = (term117 A B s f g).
Proof. exact (MK_COMB (@lem4387834) (@lem4387833 A B s f g)). Qed.
Lemma lem4387837 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4387838 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (@lem4387837 A P Q). Qed.
Lemma lem4387839 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term120 A B s f g) = (term121 A B s f g).
Proof. exact (@lem4387838 A (term84 A B s f g) (term59 A B s f g)). Qed.
Lemma lem4387840 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term107 A B s f g x) = (term74 A B s f g x).
Proof. exact (eq_refl (term107 A B s f g x)). Qed.
Lemma lem4387841 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term108 A B s f g) = (term84 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387840 A B s f g x)). Qed.
Lemma lem4387842 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387843 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term109 A B s f g) = (term85 A B s f g).
Proof. exact (MK_COMB (@lem4387842 A) (@lem4387841 A B s f g)). Qed.
Lemma lem4387844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4387845 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term122 A B s f g) = (term93 A B s f g).
Proof. exact (MK_COMB (@lem4387844) (@lem4387843 A B s f g)). Qed.
Lemma lem4387846 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term59 A B s f g).
Proof. exact (eq_refl (term59 A B s f g)). Qed.
Lemma lem4387847 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term120 A B s f g) = (term95 A B s f g).
Proof. exact (MK_COMB (@lem4387845 A B s f g) (@lem4387846 A B s f g)). Qed.
Lemma lem4387848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4387849 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term123 A B s f g) = (term124 A B s f g).
Proof. exact (MK_COMB (@lem4387848) (@lem4387847 A B s f g)). Qed.
Lemma lem4387850 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term107 A B s f g x) = (term74 A B s f g x).
Proof. exact (eq_refl (term107 A B s f g x)). Qed.
Lemma lem4387851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4387852 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term125 A B s f g x) = (term126 A B s f g x).
Proof. exact (MK_COMB (@lem4387851) (@lem4387850 A B s f g x)). Qed.
Lemma lem4387853 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term59 A B s f g).
Proof. exact (eq_refl (term59 A B s f g)). Qed.
Lemma lem4387854 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term127 A B x s f g) = (term128 A B x s f g).
Proof. exact (MK_COMB (@lem4387852 A B s f g x) (@lem4387853 A B s f g)). Qed.
Lemma lem4387855 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term129 A B s f g) = (term130 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387854 A B x s f g)). Qed.
Lemma lem4387856 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387857 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term121 A B s f g) = (term131 A B s f g).
Proof. exact (MK_COMB (@lem4387856 A) (@lem4387855 A B s f g)). Qed.
Lemma lem4387858 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term120 A B s f g) = (term121 A B s f g)) = ((term95 A B s f g) = (term131 A B s f g)).
Proof. exact (MK_COMB (@lem4387849 A B s f g) (@lem4387857 A B s f g)). Qed.
Lemma lem4387859 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term95 A B s f g) = (term131 A B s f g).
Proof. exact (EQ_MP (@lem4387858 A B s f g) (@lem4387839 A B s f g)). Qed.
Lemma lem4387860 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term102 A B s f g) = (term132 A B s f g).
Proof. exact (MK_COMB (@lem4387835 A B s f g) (@lem4387859 A B s f g)). Qed.
Lemma lem4387862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4387863 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (@lem4387862 A P Q). Qed.
Lemma lem4387864 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term135 A B s f g) = (term136 A B s f g).
Proof. exact (@lem4387863 A (term115 A B s f g) (term130 A B s f g)). Qed.
Lemma lem4387865 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term137 A B s f g x) = (term113 A B s f g x).
Proof. exact (eq_refl (term137 A B s f g x)). Qed.
Lemma lem4387866 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term138 A B s f g) = (term115 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387865 A B s f g x)). Qed.
Lemma lem4387867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387868 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term139 A B s f g) = (term116 A B s f g).
Proof. exact (MK_COMB (@lem4387867 A) (@lem4387866 A B s f g)). Qed.
Lemma lem4387869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4387870 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term140 A B s f g) = (term117 A B s f g).
Proof. exact (MK_COMB (@lem4387869) (@lem4387868 A B s f g)). Qed.
Lemma lem4387871 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term141 A B s f g x) = (term128 A B x s f g).
Proof. exact (eq_refl (term141 A B s f g x)). Qed.
Lemma lem4387872 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term142 A B s f g) = (term130 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387871 A B x s f g)). Qed.
Lemma lem4387873 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387874 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term143 A B s f g) = (term131 A B s f g).
Proof. exact (MK_COMB (@lem4387873 A) (@lem4387872 A B s f g)). Qed.
Lemma lem4387875 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term135 A B s f g) = (term132 A B s f g).
Proof. exact (MK_COMB (@lem4387870 A B s f g) (@lem4387874 A B s f g)). Qed.
Lemma lem4387876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4387877 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term144 A B s f g) = (term145 A B s f g).
Proof. exact (MK_COMB (@lem4387876) (@lem4387875 A B s f g)). Qed.
Lemma lem4387878 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term137 A B s f g x) = (term113 A B s f g x).
Proof. exact (eq_refl (term137 A B s f g x)). Qed.
Lemma lem4387879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4387880 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term146 A B s f g x) = (term147 A B s f g x).
Proof. exact (MK_COMB (@lem4387879) (@lem4387878 A B s f g x)). Qed.
Lemma lem4387881 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term141 A B s f g x) = (term128 A B x s f g).
Proof. exact (eq_refl (term141 A B s f g x)). Qed.
Lemma lem4387882 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term148 A B s f g x) = (term149 A B x s f g).
Proof. exact (MK_COMB (@lem4387880 A B s f g x) (@lem4387881 A B x s f g)). Qed.
Lemma lem4387883 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term150 A B s f g) = (term151 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387882 A B x s f g)). Qed.
Lemma lem4387884 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4387885 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term136 A B s f g) = (term152 A B s f g).
Proof. exact (MK_COMB (@lem4387884 A) (@lem4387883 A B s f g)). Qed.
Lemma lem4387886 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term135 A B s f g) = (term136 A B s f g)) = ((term132 A B s f g) = (term152 A B s f g)).
Proof. exact (MK_COMB (@lem4387877 A B s f g) (@lem4387885 A B s f g)). Qed.
Lemma lem4387887 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term132 A B s f g) = (term152 A B s f g).
Proof. exact (EQ_MP (@lem4387886 A B s f g) (@lem4387864 A B s f g)). Qed.
Lemma lem4387889 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term102 A B s f g) = (term152 A B s f g).
Proof. exact (TRANS (@lem4387860 A B s f g) (@lem4387887 A B s f g)). Qed.
Lemma lem4387890 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term68 A B s f g) = (term152 A B s f g).
Proof. exact (TRANS (@lem4387620 A B s f g) (@lem4387889 A B s f g)). Qed.
Lemma lem4387891 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term68 A B s f g) : term152 A B s f g.
Proof. exact (EQ_MP (@lem4387890 A B s f g) (@lem4387555 A B s f g h1)). Qed.
Lemma lem4387892 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term149 A B x s f g) : term149 A B x s f g.
Proof. exact (h1). Qed.
Lemma lem4387911 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term57 A B s f g x) = (term57 A B s f g x).
Proof. exact (eq_refl (term57 A B s f g x)). Qed.
Lemma lem4387912 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term58 A B s f g) = (term58 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387911 A B s f g x)). Qed.
Lemma lem4387913 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387914 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term59 A B s f g).
Proof. exact (MK_COMB (@lem4387913 A) (@lem4387912 A B s f g)). Qed.
Lemma lem4387935 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term126 A B s f g x) = (term126 A B s f g x).
Proof. exact (eq_refl (term126 A B s f g x)). Qed.
Lemma lem4387936 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term128 A B x s f g) = (term128 A B x s f g).
Proof. exact (MK_COMB (@lem4387935 A B s f g x) (@lem4387914 A B s f g)). Qed.
Lemma lem4387955 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term74 A B s f g x) = (term74 A B s f g x).
Proof. exact (eq_refl (term74 A B s f g x)). Qed.
Lemma lem4387974 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term57 A B s f g x) = (term57 A B s f g x).
Proof. exact (eq_refl (term57 A B s f g x)). Qed.
Lemma lem4387975 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term58 A B s f g) = (term58 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4387974 A B s f g x)). Qed.
Lemma lem4387976 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4387977 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term59 A B s f g).
Proof. exact (MK_COMB (@lem4387976 A) (@lem4387975 A B s f g)). Qed.
Lemma lem4387978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4387979 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term96 A B s f g) = (term96 A B s f g).
Proof. exact (MK_COMB (@lem4387978) (@lem4387977 A B s f g)). Qed.
Lemma lem4387980 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term113 A B s f g x) = (term113 A B s f g x).
Proof. exact (MK_COMB (@lem4387979 A B s f g) (@lem4387955 A B s f g x)). Qed.
Lemma lem4387981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4387982 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term147 A B s f g x) = (term147 A B s f g x).
Proof. exact (MK_COMB (@lem4387981) (@lem4387980 A B s f g x)). Qed.
Lemma lem4387983 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term149 A B x s f g) = (term149 A B x s f g).
Proof. exact (MK_COMB (@lem4387982 A B s f g x) (@lem4387936 A B x s f g)). Qed.
Lemma lem4387984 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term149 A B x s f g) : term149 A B x s f g.
Proof. exact (EQ_MP (@lem4387983 A B x s f g) (@lem4387892 A B x s f g h1)). Qed.
Lemma lem4387985 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term113 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4387986 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term128 A B x s f g.
Proof. exact (h1). Qed.
Lemma lem4387987 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term74 A B s f g x.
Proof. exact (proj2 (@lem4387985 A B s f g x h1)). Qed.
Lemma lem4387988 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term59 A B s f g.
Proof. exact (proj1 (@lem4387985 A B s f g x h1)). Qed.
Lemma lem4387991 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term59 A B s f g.
Proof. exact (proj2 (@lem4387986 A B x s f g h1)). Qed.
Lemma lem4387992 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term74 A B s f g x.
Proof. exact (proj1 (@lem4387986 A B x s f g h1)). Qed.
Lemma lem4388002 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term57 A B s f g x) = (term57 A B s f g x).
Proof. exact (eq_refl (term57 A B s f g x)). Qed.
Lemma lem4388003 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term58 A B s f g) = (term58 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4388002 A B s f g x)). Qed.
Lemma lem4388004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4388006 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term59 A B s f g).
Proof. exact (MK_COMB (@lem4388004 A) (@lem4388003 A B s f g)). Qed.
Lemma lem4388007 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term59 A B s f g.
Proof. exact (EQ_MP (@lem4388006 A B s f g) (@lem4387988 A B s f g x h1)). Qed.
Lemma lem4388023 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term57 A B s f g x) = (term57 A B s f g x).
Proof. exact (eq_refl (term57 A B s f g x)). Qed.
Lemma lem4388024 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term58 A B s f g) = (term58 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4388023 A B s f g x)). Qed.
Lemma lem4388025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4388027 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term59 A B s f g).
Proof. exact (MK_COMB (@lem4388025 A) (@lem4388024 A B s f g)). Qed.
Lemma lem4388028 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term59 A B s f g.
Proof. exact (EQ_MP (@lem4388027 A B s f g) (@lem4387991 A B x s f g h1)). Qed.
Lemma lem4388037 {A B : Type'} (_50119 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term81 A B s f g _50119.
Proof. exact (@lem4388007 A B s f g x h1 _50119). Qed.
Lemma lem4388038 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50119 : A) : (term81 A B s f g _50119) = (term57 A B s f g _50119).
Proof. exact (eq_refl (term81 A B s f g _50119)). Qed.
Lemma lem4388040 {A B : Type'} (_50120 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term81 A B s f g _50120.
Proof. exact (@lem4388028 A B x s f g h1 _50120). Qed.
Lemma lem4388041 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50120 : A) : (term81 A B s f g _50120) = (term57 A B s f g _50120).
Proof. exact (eq_refl (term81 A B s f g _50120)). Qed.
Lemma lem4388048 {A B : Type'} (_50119 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term57 A B s f g _50119.
Proof. exact (EQ_MP (@lem4388038 A B s f g _50119) (@lem4388037 A B _50119 s f g x h1)). Qed.
Lemma lem4388052 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term70 A B f g x.
Proof. exact (proj2 (@lem4387987 A B s f g x h1)). Qed.
Lemma lem4388058 {A B : Type'} (_50120 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term57 A B s f g _50120.
Proof. exact (EQ_MP (@lem4388041 A B s f g _50120) (@lem4388040 A B _50120 x s f g h1)). Qed.
Lemma lem4388062 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term70 A B f g x.
Proof. exact (proj2 (@lem4387992 A B x s f g h1)). Qed.
Lemma lem4388105 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : @IN A x s.
Proof. exact (proj1 (@lem4387987 A B s f g x h1)). Qed.
Lemma lem4388106 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term153 A x s.
Proof. exact (fun h0 : term76 A x s => @lem4388105 A B s f g x h1). Qed.
Lemma lem4388108 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4388109 {A : Type'} (x : A) (s : A -> Prop) : (term153 A x s) = (@IN A x s).
Proof. exact (@lem4388108 (@IN A x s)). Qed.
Lemma lem4388110 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : @IN A x s.
Proof. exact (EQ_MP (@lem4388109 A x s) (@lem4388106 A B s f g x h1)). Qed.
Lemma lem4388116 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4388117 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : (term57 A B s f g _50119) = (term155 A B f g _50119 s).
Proof. exact (@lem4388116 ((f _50119) = (g _50119)) (term76 A _50119 s)). Qed.
Lemma lem4388125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4388126 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : (term156 A B s f g _50119) = (term157 A B f g _50119 s).
Proof. exact (MK_COMB (@lem4388125) (@lem4388117 A B f g _50119 s)). Qed.
Lemma lem4388134 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : (term155 A B f g _50119 s) = (term155 A B f g _50119 s).
Proof. exact (eq_refl (term155 A B f g _50119 s)). Qed.
Lemma lem4388135 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : ((term57 A B s f g _50119) = (term155 A B f g _50119 s)) = ((term155 A B f g _50119 s) = (term155 A B f g _50119 s)).
Proof. exact (MK_COMB (@lem4388126 A B f g _50119 s) (@lem4388134 A B f g _50119 s)). Qed.
Lemma lem4388137 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4388138 (x : Prop) : (x = x) = True.
Proof. exact (@lem4388137 Prop x). Qed.
Lemma lem4388139 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : ((term155 A B f g _50119 s) = (term155 A B f g _50119 s)) = True.
Proof. exact (@lem4388138 (term155 A B f g _50119 s)). Qed.
Lemma lem4388140 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : ((term57 A B s f g _50119) = (term155 A B f g _50119 s)) = True.
Proof. exact (TRANS (@lem4388135 A B f g _50119 s) (@lem4388139 A B f g _50119 s)). Qed.
Lemma lem4388141 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : True = ((term57 A B s f g _50119) = (term155 A B f g _50119 s)).
Proof. exact (SYM (@lem4388140 A B f g _50119 s)). Qed.
Lemma lem4388142 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) (s : A -> Prop) : (term57 A B s f g _50119) = (term155 A B f g _50119 s).
Proof. exact (EQ_MP (@lem4388141 A B f g _50119 s) (@lem0)). Qed.
Lemma lem4388143 {A B : Type'} (_50119 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term155 A B f g _50119 s.
Proof. exact (EQ_MP (@lem4388142 A B f g _50119 s) (@lem4388048 A B _50119 s f g x h1)). Qed.
Lemma lem4388145 (b : Prop) (a : Prop) : (a \/ b) = (term158 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4388146 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50119 : A) : (term155 A B f g _50119 s) = (term159 A B s f g _50119).
Proof. exact (@lem4388145 (term76 A _50119 s) ((f _50119) = (g _50119))). Qed.
Lemma lem4388148 (a : Prop) : (term26 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4388149 {A : Type'} (_50119 : A) (s : A -> Prop) : (term69 A _50119 s) = (@IN A _50119 s).
Proof. exact (@lem4388148 (@IN A _50119 s)). Qed.
Lemma lem4388150 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4388151 {A : Type'} (_50119 : A) (s : A -> Prop) : (term160 A _50119 s) = (term161 A _50119 s).
Proof. exact (MK_COMB (@lem4388150) (@lem4388149 A _50119 s)). Qed.
Lemma lem4388152 {A B : Type'} (f : A -> B) (g : A -> B) (_50119 : A) : ((f _50119) = (g _50119)) = ((f _50119) = (g _50119)).
Proof. exact (eq_refl ((f _50119) = (g _50119))). Qed.
Lemma lem4388153 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50119 : A) : (term159 A B s f g _50119) = (term39 A B s f g _50119).
Proof. exact (MK_COMB (@lem4388151 A _50119 s) (@lem4388152 A B f g _50119)). Qed.
Lemma lem4388154 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50119 : A) : (term155 A B f g _50119 s) = (term39 A B s f g _50119).
Proof. exact (TRANS (@lem4388146 A B s f g _50119) (@lem4388153 A B s f g _50119)). Qed.
Lemma lem4388157 {A B : Type'} (_50119 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term39 A B s f g _50119.
Proof. exact (EQ_MP (@lem4388154 A B s f g _50119) (@lem4388143 A B _50119 s f g x h1)). Qed.
Lemma lem4388158 {A B : Type'} (_50119 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term39 A B s f g _50119.
Proof. exact (@lem4388157 A B _50119 s f g x h1). Qed.
Lemma lem4388159 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term39 A B s f g x.
Proof. exact (@lem4388158 A B x s f g x h1). Qed.
Lemma lem4388162 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : (f x) = (g x).
Proof. exact (@lem4388159 A B s f g x h1 (@lem4388110 A B s f g x h1)). Qed.
Lemma lem4388163 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term162 A B f g x.
Proof. exact (fun h0 : term70 A B f g x => @lem4388162 A B s f g x h1). Qed.
Lemma lem4388165 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4388166 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term162 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem4388165 ((f x) = (g x))). Qed.
Lemma lem4388167 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4388166 A B f g x) (@lem4388163 A B s f g x h1)). Qed.
Lemma lem4388170 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4388172 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term70 A B f g x) = (term163 A B f g x).
Proof. exact (@lem4388170 ((f x) = (g x))). Qed.
Lemma lem4388175 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term163 A B f g x.
Proof. exact (EQ_MP (@lem4388172 A B f g x) (@lem4388052 A B s f g x h1)). Qed.
Lemma lem4388178 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : False.
Proof. exact (@lem4388175 A B s f g x h1 (@lem4388167 A B s f g x h1)). Qed.
Lemma lem4388179 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : term164.
Proof. exact (fun h0 : ~ False => @lem4388178 A B s f g x h1). Qed.
Lemma lem4388181 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4388182 : term164 = False.
Proof. exact (@lem4388181 False). Qed.
Lemma lem4388183 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term113 A B s f g x) : False.
Proof. exact (EQ_MP (@lem4388182) (@lem4388179 A B s f g x h1)). Qed.
Lemma lem4388226 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : @IN A x s.
Proof. exact (proj1 (@lem4387992 A B x s f g h1)). Qed.
Lemma lem4388227 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term153 A x s.
Proof. exact (fun h0 : term76 A x s => @lem4388226 A B x s f g h1). Qed.
Lemma lem4388229 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4388230 {A : Type'} (x : A) (s : A -> Prop) : (term153 A x s) = (@IN A x s).
Proof. exact (@lem4388229 (@IN A x s)). Qed.
Lemma lem4388231 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : @IN A x s.
Proof. exact (EQ_MP (@lem4388230 A x s) (@lem4388227 A B x s f g h1)). Qed.
Lemma lem4388237 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4388238 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : (term57 A B s f g _50120) = (term155 A B f g _50120 s).
Proof. exact (@lem4388237 ((f _50120) = (g _50120)) (term76 A _50120 s)). Qed.
Lemma lem4388246 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4388247 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : (term156 A B s f g _50120) = (term157 A B f g _50120 s).
Proof. exact (MK_COMB (@lem4388246) (@lem4388238 A B f g _50120 s)). Qed.
Lemma lem4388255 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : (term155 A B f g _50120 s) = (term155 A B f g _50120 s).
Proof. exact (eq_refl (term155 A B f g _50120 s)). Qed.
Lemma lem4388256 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : ((term57 A B s f g _50120) = (term155 A B f g _50120 s)) = ((term155 A B f g _50120 s) = (term155 A B f g _50120 s)).
Proof. exact (MK_COMB (@lem4388247 A B f g _50120 s) (@lem4388255 A B f g _50120 s)). Qed.
Lemma lem4388258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4388259 (x : Prop) : (x = x) = True.
Proof. exact (@lem4388258 Prop x). Qed.
Lemma lem4388260 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : ((term155 A B f g _50120 s) = (term155 A B f g _50120 s)) = True.
Proof. exact (@lem4388259 (term155 A B f g _50120 s)). Qed.
Lemma lem4388261 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : ((term57 A B s f g _50120) = (term155 A B f g _50120 s)) = True.
Proof. exact (TRANS (@lem4388256 A B f g _50120 s) (@lem4388260 A B f g _50120 s)). Qed.
Lemma lem4388262 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : True = ((term57 A B s f g _50120) = (term155 A B f g _50120 s)).
Proof. exact (SYM (@lem4388261 A B f g _50120 s)). Qed.
Lemma lem4388263 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) (s : A -> Prop) : (term57 A B s f g _50120) = (term155 A B f g _50120 s).
Proof. exact (EQ_MP (@lem4388262 A B f g _50120 s) (@lem0)). Qed.
Lemma lem4388264 {A B : Type'} (_50120 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term155 A B f g _50120 s.
Proof. exact (EQ_MP (@lem4388263 A B f g _50120 s) (@lem4388058 A B _50120 x s f g h1)). Qed.
Lemma lem4388266 (b : Prop) (a : Prop) : (a \/ b) = (term158 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4388267 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50120 : A) : (term155 A B f g _50120 s) = (term159 A B s f g _50120).
Proof. exact (@lem4388266 (term76 A _50120 s) ((f _50120) = (g _50120))). Qed.
Lemma lem4388269 (a : Prop) : (term26 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4388270 {A : Type'} (_50120 : A) (s : A -> Prop) : (term69 A _50120 s) = (@IN A _50120 s).
Proof. exact (@lem4388269 (@IN A _50120 s)). Qed.
Lemma lem4388271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4388272 {A : Type'} (_50120 : A) (s : A -> Prop) : (term160 A _50120 s) = (term161 A _50120 s).
Proof. exact (MK_COMB (@lem4388271) (@lem4388270 A _50120 s)). Qed.
Lemma lem4388273 {A B : Type'} (f : A -> B) (g : A -> B) (_50120 : A) : ((f _50120) = (g _50120)) = ((f _50120) = (g _50120)).
Proof. exact (eq_refl ((f _50120) = (g _50120))). Qed.
Lemma lem4388274 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50120 : A) : (term159 A B s f g _50120) = (term39 A B s f g _50120).
Proof. exact (MK_COMB (@lem4388272 A _50120 s) (@lem4388273 A B f g _50120)). Qed.
Lemma lem4388275 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50120 : A) : (term155 A B f g _50120 s) = (term39 A B s f g _50120).
Proof. exact (TRANS (@lem4388267 A B s f g _50120) (@lem4388274 A B s f g _50120)). Qed.
Lemma lem4388278 {A B : Type'} (_50120 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term39 A B s f g _50120.
Proof. exact (EQ_MP (@lem4388275 A B s f g _50120) (@lem4388264 A B _50120 x s f g h1)). Qed.
Lemma lem4388279 {A B : Type'} (_50120 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term39 A B s f g _50120.
Proof. exact (@lem4388278 A B _50120 x s f g h1). Qed.
Lemma lem4388280 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term39 A B s f g x.
Proof. exact (@lem4388279 A B x x s f g h1). Qed.
Lemma lem4388283 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : (f x) = (g x).
Proof. exact (@lem4388280 A B x s f g h1 (@lem4388231 A B x s f g h1)). Qed.
Lemma lem4388284 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term162 A B f g x.
Proof. exact (fun h0 : term70 A B f g x => @lem4388283 A B x s f g h1). Qed.
Lemma lem4388286 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4388287 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term162 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem4388286 ((f x) = (g x))). Qed.
Lemma lem4388288 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4388287 A B f g x) (@lem4388284 A B x s f g h1)). Qed.
Lemma lem4388291 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4388293 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term70 A B f g x) = (term163 A B f g x).
Proof. exact (@lem4388291 ((f x) = (g x))). Qed.
Lemma lem4388296 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term163 A B f g x.
Proof. exact (EQ_MP (@lem4388293 A B f g x) (@lem4388062 A B x s f g h1)). Qed.
Lemma lem4388299 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : False.
Proof. exact (@lem4388296 A B x s f g h1 (@lem4388288 A B x s f g h1)). Qed.
Lemma lem4388300 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : term164.
Proof. exact (fun h0 : ~ False => @lem4388299 A B x s f g h1). Qed.
Lemma lem4388302 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4388303 : term164 = False.
Proof. exact (@lem4388302 False). Qed.
Lemma lem4388304 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term128 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4388303) (@lem4388300 A B x s f g h1)). Qed.
Lemma lem4388305 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term149 A B x s f g) : False.
Proof. exact (or_elim (@lem4387984 A B x s f g h1) (fun h0 : term113 A B s f g x => @lem4388183 A B s f g x h0) (fun h0 : term128 A B x s f g => @lem4388304 A B x s f g h0)). Qed.
Lemma lem4388306 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term149 A B x s f g) : (term149 A B x s f g) = False.
Proof. exact (prop_ext (fun h2 : term149 A B x s f g => @lem4388305 A B x s f g h1) (fun h2 : False => @lem4387984 A B x s f g h1)). Qed.
Lemma lem4388307 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term149 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4388306 A B x s f g h1) (@lem4387984 A B x s f g h1)). Qed.
Lemma lem4388308 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term68 A B s f g) : False.
Proof. exact (ex_elim (@lem4387891 A B s f g h1) (fun x : A => fun h0 : term151 A B s f g x => @lem4388307 A B x s f g h0)). Qed.
Lemma lem4388309 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term68 A B s f g) : (term68 A B s f g) = False.
Proof. exact (prop_ext (fun h2 : term68 A B s f g => @lem4388308 A B s f g h1) (fun h2 : False => @lem4387555 A B s f g h1)). Qed.
Lemma lem4388310 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term68 A B s f g) : False.
Proof. exact (EQ_MP (@lem4388309 A B s f g h1) (@lem4387555 A B s f g h1)). Qed.
Lemma lem4388311 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term67 A B s f g.
Proof. exact (fun h0 : term68 A B s f g => @lem4388310 A B s f g h0). Qed.
Lemma lem4388312 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term59 A B s f g) = (term18 A B s f g).
Proof. exact (EQ_MP (@lem4387554 A B s f g) (@lem4388311 A B s f g)). Qed.
Lemma lem4388317 {A B : Type'} (f : A -> B) (g : A -> B) : term62 A B f g.
Proof. exact (fun s : A -> Prop => @lem4388312 A B s f g). Qed.
Lemma lem4388322 {A B : Type'} (g : A -> B) : term64 A B g.
Proof. exact (fun f : A -> B => @lem4388317 A B f g). Qed.
Lemma lem4388327 {A B : Type'} : term66 A B.
Proof. exact (fun g : A -> B => @lem4388322 A B g). Qed.
Lemma lem4388328 {A B : Type'} : term37 A B.
Proof. exact (EQ_MP (@lem4387550 A B) (@lem4388327 A B)). Qed.
Lemma lem4388329 {A B : Type'} (g : A -> B) : term165 A B g.
Proof. exact (@lem4388328 A B g). Qed.
Lemma lem4388330 {A B : Type'} (g : A -> B) : (term165 A B g) = (term33 A B g).
Proof. exact (eq_refl (term165 A B g)). Qed.
Lemma lem4388331 {A B : Type'} (g : A -> B) : term33 A B g.
Proof. exact (EQ_MP (@lem4388330 A B g) (@lem4388329 A B g)). Qed.
Lemma lem4388332 {A B : Type'} (g : A -> B) (f : A -> B) : term166 A B g f.
Proof. exact (@lem4388331 A B g f). Qed.
Lemma lem4388333 {A B : Type'} (f : A -> B) (g : A -> B) : (term166 A B g f) = (term29 A B f g).
Proof. exact (eq_refl (term166 A B g f)). Qed.
Lemma lem4388334 {A B : Type'} (f : A -> B) (g : A -> B) : term29 A B f g.
Proof. exact (EQ_MP (@lem4388333 A B f g) (@lem4388332 A B g f)). Qed.
Lemma lem4388335 {A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) : term167 A B f g s.
Proof. exact (@lem4388334 A B f g s). Qed.
Lemma lem4388336 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term167 A B f g s) = (term20 A B s f g).
Proof. exact (eq_refl (term167 A B f g s)). Qed.
Lemma lem4388337 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term20 A B s f g.
Proof. exact (EQ_MP (@lem4388336 A B s f g) (@lem4388335 A B f g s)). Qed.
Lemma lem4388339 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term20 A B s f g.
Proof. exact (@lem4387337 A B s f g (@lem4388337 A B s f g)). Qed.
Lemma lem4388340 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term21 A B s f g) : False.
Proof. exact (@lem4388339 A B s f g (@lem4387321 A B s f g h1)). Qed.
Lemma lem4388341 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term21 A B s f g) : (term21 A B s f g) = False.
Proof. exact (prop_ext (fun h2 : term21 A B s f g => @lem4388340 A B s f g h1) (fun h2 : False => @lem4387321 A B s f g h1)). Qed.
Lemma lem4388342 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term21 A B s f g) : False.
Proof. exact (EQ_MP (@lem4388341 A B s f g h1) (@lem4387321 A B s f g h1)). Qed.
Lemma lem4388343 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term20 A B s f g.
Proof. exact (fun h0 : term21 A B s f g => @lem4388342 A B s f g h0). Qed.
Lemma lem4388344 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term15 A B f s g) = (term18 A B s f g).
Proof. exact (EQ_MP (@lem4387320 A B s f g) (@lem4388343 A B s f g)). Qed.
Lemma lem4388345 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term18 A B s f g).
Proof. exact (EQ_MP (@lem4387316 A B s f g) (@lem4388344 A B s f g)). Qed.
Lemma lem4388350 {A B : Type'} (s : A -> Prop) (f : A -> B) : term168 A B s f.
Proof. exact (fun g : A -> B => @lem4388345 A B s f g). Qed.
Lemma lem4388355 {A B : Type'} (s : A -> Prop) : term169 A B s.
Proof. exact (fun f : A -> B => @lem4388350 A B s f). Qed.
Lemma lem4388360 {A B : Type'} : term170 A B.
Proof. exact (fun s : A -> Prop => @lem4388355 A B s). Qed.
