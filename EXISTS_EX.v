Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_EX_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1101587_spec.
Require Import thm1101588_spec.
Require Import thm1101596_spec.
Require Import thm1101597_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
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
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem1139271 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1139272 {_26886 : Type'} (P : type1143 _26886) : term0 _26886 P.
Proof. exact (@lem1139271 _26886 P). Qed.
Lemma lem1139273 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : term1 _26886 _26887 P.
Proof. exact (@lem1139272 _26886 (term2 _26886 _26887 P)). Qed.
Lemma lem1139274 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term3 _26886 _26887 P) = ((term4 _26886 _26887 P) = (term5 _26886 _26887 P)).
Proof. exact (eq_refl (term3 _26886 _26887 P)). Qed.
Lemma lem1139275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1139276 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term6 _26886 _26887 P) = (term7 _26886 _26887 P).
Proof. exact (MK_COMB (@lem1139275) (@lem1139274 _26886 _26887 P)). Qed.
Lemma lem1139277 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term8 _26886 _26887 P t) = ((term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)).
Proof. exact (eq_refl (term8 _26886 _26887 P t)). Qed.
Lemma lem1139278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139279 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term11 _26886 _26887 P t) = (term12 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139278) (@lem1139277 _26886 _26887 P t)). Qed.
Lemma lem1139280 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) (t : list _26886) : (term13 _26886 _26887 P h t) = ((term14 _26886 _26887 P h t) = (term15 _26886 _26887 P h t)).
Proof. exact (eq_refl (term13 _26886 _26887 P h t)). Qed.
Lemma lem1139281 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) (t : list _26886) : (term16 _26886 _26887 P h t) = (term17 _26886 _26887 P h t).
Proof. exact (MK_COMB (@lem1139279 _26886 _26887 P t) (@lem1139280 _26886 _26887 P h t)). Qed.
Lemma lem1139282 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term18 _26886 _26887 P h) = (term19 _26886 _26887 P h).
Proof. exact (fun_ext (fun t : list _26886 => @lem1139281 _26886 _26887 P h t)). Qed.
Lemma lem1139283 {_26886 : Type'} : (@all (list _26886)) = (@all (list _26886)).
Proof. exact (eq_refl (@all (list _26886))). Qed.
Lemma lem1139284 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term20 _26886 _26887 P h) = (term21 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139283 _26886) (@lem1139282 _26886 _26887 P h)). Qed.
Lemma lem1139285 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term22 _26886 _26887 P) = (term23 _26886 _26887 P).
Proof. exact (fun_ext (fun h : _26886 => @lem1139284 _26886 _26887 P h)). Qed.
Lemma lem1139286 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139287 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term24 _26886 _26887 P) = (term25 _26886 _26887 P).
Proof. exact (MK_COMB (@lem1139286 _26886) (@lem1139285 _26886 _26887 P)). Qed.
Lemma lem1139288 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term26 _26886 _26887 P) = (term27 _26886 _26887 P).
Proof. exact (MK_COMB (@lem1139276 _26886 _26887 P) (@lem1139287 _26886 _26887 P)). Qed.
Lemma lem1139289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139290 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term28 _26886 _26887 P) = (term29 _26886 _26887 P).
Proof. exact (MK_COMB (@lem1139289) (@lem1139288 _26886 _26887 P)). Qed.
Lemma lem1139291 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (l : list _26886) : (term8 _26886 _26887 P l) = ((term9 _26886 _26887 P l) = (term10 _26886 _26887 P l)).
Proof. exact (eq_refl (term8 _26886 _26887 P l)). Qed.
Lemma lem1139292 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term30 _26886 _26887 P) = (term2 _26886 _26887 P).
Proof. exact (fun_ext (fun l : list _26886 => @lem1139291 _26886 _26887 P l)). Qed.
Lemma lem1139293 {_26886 : Type'} : (@all (list _26886)) = (@all (list _26886)).
Proof. exact (eq_refl (@all (list _26886))). Qed.
Lemma lem1139294 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term31 _26886 _26887 P) = (term32 _26886 _26887 P).
Proof. exact (MK_COMB (@lem1139293 _26886) (@lem1139292 _26886 _26887 P)). Qed.
Lemma lem1139295 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term1 _26886 _26887 P) = (term33 _26886 _26887 P).
Proof. exact (MK_COMB (@lem1139290 _26886 _26887 P) (@lem1139294 _26886 _26887 P)). Qed.
Lemma lem1139296 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : term33 _26886 _26887 P.
Proof. exact (EQ_MP (@lem1139295 _26886 _26887 P) (@lem1139273 _26886 _26887 P)). Qed.
Lemma lem1139297 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (h1 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t).
Proof. exact (h1). Qed.
Lemma lem1139307 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1139308 {_26886 : Type'} (P : _26886 -> Prop) : (@EX _26886 P (@nil _26886)) = False.
Proof. exact (@lem1139307 _26886 P). Qed.
Lemma lem1139309 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (term34 _26886 _26887 P x) = False.
Proof. exact (@lem1139308 _26886 (P x)). Qed.
Lemma lem1139310 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term35 _26886 _26887 P) = (term36 _26887).
Proof. exact (fun_ext (fun x : _26887 => @lem1139309 _26886 _26887 P x)). Qed.
Lemma lem1139311 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139312 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term4 _26886 _26887 P) = (term37 _26887).
Proof. exact (MK_COMB (@lem1139311 _26887) (@lem1139310 _26886 _26887 P)). Qed.
Lemma lem1139314 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1139315 {_26887 : Type'} (t : Prop) : (term38 _26887 t) = t.
Proof. exact (@lem1139314 _26887 t). Qed.
Lemma lem1139316 {_26887 : Type'} : (term37 _26887) = False.
Proof. exact (@lem1139315 _26887 False). Qed.
Lemma lem1139317 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term4 _26886 _26887 P) = False.
Proof. exact (TRANS (@lem1139312 _26886 _26887 P) (@lem1139316 _26887)). Qed.
Lemma lem1139318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139319 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term39 _26886 _26887 P) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1139318) (@lem1139317 _26886 _26887 P)). Qed.
Lemma lem1139321 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1139322 {_26886 : Type'} (P : _26886 -> Prop) : (@EX _26886 P (@nil _26886)) = False.
Proof. exact (@lem1139321 _26886 P). Qed.
Lemma lem1139323 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term5 _26886 _26887 P) = False.
Proof. exact (@lem1139322 _26886 (term40 _26886 _26887 P)). Qed.
Lemma lem1139324 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : ((term4 _26886 _26887 P) = (term5 _26886 _26887 P)) = (False = False).
Proof. exact (MK_COMB (@lem1139319 _26886 _26887 P) (@lem1139323 _26886 _26887 P)). Qed.
Lemma lem1139326 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1139327 : (False = False) = (~ False).
Proof. exact (@lem1139326 False). Qed.
Lemma lem1139329 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1139330 : (False = False) = True.
Proof. exact (TRANS (@lem1139327) (@lem1139329)). Qed.
Lemma lem1139331 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : ((term4 _26886 _26887 P) = (term5 _26886 _26887 P)) = True.
Proof. exact (TRANS (@lem1139324 _26886 _26887 P) (@lem1139330)). Qed.
Lemma lem1139332 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : True = ((term4 _26886 _26887 P) = (term5 _26886 _26887 P)).
Proof. exact (SYM (@lem1139331 _26886 _26887 P)). Qed.
Lemma lem1139333 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term4 _26886 _26887 P) = (term5 _26886 _26887 P).
Proof. exact (EQ_MP (@lem1139332 _26886 _26887 P) (@lem0)). Qed.
Lemma lem1139343 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term41 _25328 P h t) = (term42 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1139344 {_26886 : Type'} (h : _26886) (P : _26886 -> Prop) (t : list _26886) : (term41 _26886 P h t) = (term42 _26886 h P t).
Proof. exact (@lem1139343 _26886 h P t). Qed.
Lemma lem1139345 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term43 _26886 _26887 P x h t) = (term44 _26886 _26887 h P x t).
Proof. exact (@lem1139344 _26886 h (P x) t). Qed.
Lemma lem1139348 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term45 _26886 _26887 P h t) = (term46 _26886 _26887 h P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1139345 _26886 _26887 h P x t)). Qed.
Lemma lem1139349 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139350 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term14 _26886 _26887 P h t) = (term47 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139349 _26887) (@lem1139348 _26886 _26887 h P t)). Qed.
Lemma lem1139355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139356 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term48 _26886 _26887 P h t) = (term49 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139355) (@lem1139350 _26886 _26887 h P t)). Qed.
Lemma lem1139358 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term41 _25328 P h t) = (term42 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1139359 {_26886 : Type'} (h : _26886) (P : _26886 -> Prop) (t : list _26886) : (term41 _26886 P h t) = (term42 _26886 h P t).
Proof. exact (@lem1139358 _26886 h P t). Qed.
Lemma lem1139360 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term15 _26886 _26887 P h t) = (term50 _26886 _26887 h P t).
Proof. exact (@lem1139359 _26886 h (term40 _26886 _26887 P) t). Qed.
Lemma lem1139364 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1139365 {_26886 : Type'} (f : _26886 -> Prop) (y : _26886) : (term52 _26886 f y) = (f y).
Proof. exact (@lem1139364 _26886 Prop f y). Qed.
Lemma lem1139366 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term53 _26886 _26887 P h) = (term54 _26886 _26887 P h).
Proof. exact (@lem1139365 _26886 (term40 _26886 _26887 P) h). Qed.
Lemma lem1139367 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term54 _26886 _26887 P s) = (term55 _26886 _26887 P s).
Proof. exact (eq_refl (term54 _26886 _26887 P s)). Qed.
Lemma lem1139368 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term56 _26886 _26887 P) = (term40 _26886 _26887 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139367 _26886 _26887 P s)). Qed.
Lemma lem1139369 {_26886 : Type'} (h : _26886) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1139370 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term53 _26886 _26887 P h) = (term54 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139368 _26886 _26887 P) (@lem1139369 _26886 h)). Qed.
Lemma lem1139371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139372 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term57 _26886 _26887 P h) = (term58 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139371) (@lem1139370 _26886 _26887 P h)). Qed.
Lemma lem1139373 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term54 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (eq_refl (term54 _26886 _26887 P h)). Qed.
Lemma lem1139374 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : ((term53 _26886 _26887 P h) = (term54 _26886 _26887 P h)) = ((term54 _26886 _26887 P h) = (term55 _26886 _26887 P h)).
Proof. exact (MK_COMB (@lem1139372 _26886 _26887 P h) (@lem1139373 _26886 _26887 P h)). Qed.
Lemma lem1139375 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term54 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (EQ_MP (@lem1139374 _26886 _26887 P h) (@lem1139366 _26886 _26887 P h)). Qed.
Lemma lem1139380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139381 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term59 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139380) (@lem1139375 _26886 _26887 P h)). Qed.
Lemma lem1139386 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term10 _26886 _26887 P t) = (term10 _26886 _26887 P t).
Proof. exact (eq_refl (term10 _26886 _26887 P t)). Qed.
Lemma lem1139387 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term50 _26886 _26887 h P t) = (term61 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139381 _26886 _26887 P h) (@lem1139386 _26886 _26887 P t)). Qed.
Lemma lem1139390 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term15 _26886 _26887 P h t) = (term61 _26886 _26887 h P t).
Proof. exact (TRANS (@lem1139360 _26886 _26887 h P t) (@lem1139387 _26886 _26887 h P t)). Qed.
Lemma lem1139391 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : ((term14 _26886 _26887 P h t) = (term15 _26886 _26887 P h t)) = ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)).
Proof. exact (MK_COMB (@lem1139356 _26886 _26887 h P t) (@lem1139390 _26886 _26887 h P t)). Qed.
Lemma lem1139394 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) (t : list _26886) : ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)) = ((term14 _26886 _26887 P h t) = (term15 _26886 _26887 P h t)).
Proof. exact (SYM (@lem1139391 _26886 _26887 h P t)). Qed.
Lemma lem1139396 (p : Prop) : p = (term62 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1139397 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)) = (term63 _26886 _26887 h P t).
Proof. exact (@lem1139396 ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t))). Qed.
Lemma lem1139398 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term63 _26886 _26887 h P t) = ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)).
Proof. exact (SYM (@lem1139397 _26886 _26887 h P t)). Qed.
Lemma lem1139399 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term64 _26886 _26887 h P t) : term64 _26886 _26887 h P t.
Proof. exact (h1). Qed.
Lemma lem1139402 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term65 _26886 _26887 h P t) : term65 _26886 _26887 h P t.
Proof. exact (h1). Qed.
Lemma lem1139403 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : term66 _26886 _26887 h P t.
Proof. exact (fun h0 : term65 _26886 _26887 h P t => @lem1139402 _26886 _26887 h P t h0). Qed.
Lemma lem1139404 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term66 _26886 _26887 h P t) : term66 _26886 _26887 h P t.
Proof. exact (h1). Qed.
Lemma lem1139405 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term65 _26886 _26887 h P t) : term65 _26886 _26887 h P t.
Proof. exact (h1). Qed.
Lemma lem1139406 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term65 _26886 _26887 h P t) (h2 : term66 _26886 _26887 h P t) : term65 _26886 _26887 h P t.
Proof. exact (@lem1139404 _26886 _26887 h P t h2 (@lem1139405 _26886 _26887 h P t h1)). Qed.
Lemma lem1139407 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term65 _26886 _26887 h P t) : term67 _26886 _26887 h P t.
Proof. exact (fun h0 : term66 _26886 _26887 h P t => @lem1139406 _26886 _26887 h P t h1 h0). Qed.
Lemma lem1139408 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term66 _26886 _26887 h P t) : term66 _26886 _26887 h P t.
Proof. exact (h1). Qed.
Lemma lem1139409 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term65 _26886 _26887 h P t) (h2 : term66 _26886 _26887 h P t) : term65 _26886 _26887 h P t.
Proof. exact (@lem1139407 _26886 _26887 h P t h1 (@lem1139408 _26886 _26887 h P t h2)). Qed.
Lemma lem1139410 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term66 _26886 _26887 h P t) : term66 _26886 _26887 h P t.
Proof. exact (fun h0 : term65 _26886 _26887 h P t => @lem1139409 _26886 _26887 h P t h0 h1). Qed.
Lemma lem1139411 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : term68 _26886 _26887 h P t.
Proof. exact (fun h0 : term66 _26886 _26887 h P t => @lem1139410 _26886 _26887 h P t h0). Qed.
Lemma lem1139414 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : term66 _26886 _26887 h P t.
Proof. exact (@lem1139411 _26886 _26887 h P t (@lem1139403 _26886 _26887 h P t)). Qed.
Lemma lem1139415 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : term66 _26886 _26887 h P t.
Proof. exact (@lem1139414 _26886 _26887 h P t). Qed.
Lemma lem1139439 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1139440 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term63 _26886 _26887 h P t) = (term69 _26886 _26887 h P t).
Proof. exact (@lem1139439 (term64 _26886 _26887 h P t)). Qed.
Lemma lem1139442 (t : Prop) : (term70 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1139443 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term69 _26886 _26887 h P t) = ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)).
Proof. exact (@lem1139442 ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t))). Qed.
Lemma lem1139444 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term63 _26886 _26887 h P t) = ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)).
Proof. exact (TRANS (@lem1139440 _26886 _26887 h P t) (@lem1139443 _26886 _26887 h P t)). Qed.
Lemma lem1139446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem1139447 {_26887 : Type'} (P : _26887 -> Prop) (Q : _26887 -> Prop) : (term71 _26887 P Q) = (term72 _26887 P Q).
Proof. exact (@lem1139446 _26887 P Q). Qed.
Lemma lem1139448 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term73 _26886 _26887 h P t) = (term74 _26886 _26887 h P t).
Proof. exact (@lem1139447 _26887 (term75 _26886 _26887 P h) (term76 _26886 _26887 P t)). Qed.
Lemma lem1139449 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1139450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139451 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term78 _26886 _26887 P h x) = (term79 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1139450) (@lem1139449 _26886 _26887 P x h)). Qed.
Lemma lem1139452 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1139453 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term82 _26886 _26887 h P t x) = (term44 _26886 _26887 h P x t).
Proof. exact (MK_COMB (@lem1139451 _26886 _26887 P x h) (@lem1139452 _26886 _26887 P x t)). Qed.
Lemma lem1139454 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term83 _26886 _26887 h P t) = (term46 _26886 _26887 h P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1139453 _26886 _26887 h P x t)). Qed.
Lemma lem1139455 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139456 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term73 _26886 _26887 h P t) = (term47 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139455 _26887) (@lem1139454 _26886 _26887 h P t)). Qed.
Lemma lem1139457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139458 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term84 _26886 _26887 h P t) = (term49 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139457) (@lem1139456 _26886 _26887 h P t)). Qed.
Lemma lem1139459 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1139460 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term85 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1139459 _26886 _26887 P x h)). Qed.
Lemma lem1139461 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139462 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term86 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139461 _26887) (@lem1139460 _26886 _26887 P h)). Qed.
Lemma lem1139463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139464 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term87 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139463) (@lem1139462 _26886 _26887 P h)). Qed.
Lemma lem1139465 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1139466 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term88 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1139465 _26886 _26887 P x t)). Qed.
Lemma lem1139467 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139468 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term89 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139467 _26887) (@lem1139466 _26886 _26887 P t)). Qed.
Lemma lem1139469 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term74 _26886 _26887 h P t) = (term90 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139464 _26886 _26887 P h) (@lem1139468 _26886 _26887 P t)). Qed.
Lemma lem1139470 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : ((term73 _26886 _26887 h P t) = (term74 _26886 _26887 h P t)) = ((term47 _26886 _26887 h P t) = (term90 _26886 _26887 h P t)).
Proof. exact (MK_COMB (@lem1139458 _26886 _26887 h P t) (@lem1139469 _26886 _26887 h P t)). Qed.
Lemma lem1139471 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term47 _26886 _26887 h P t) = (term90 _26886 _26887 h P t).
Proof. exact (EQ_MP (@lem1139470 _26886 _26887 h P t) (@lem1139448 _26886 _26887 h P t)). Qed.
Lemma lem1139482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139483 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term49 _26886 _26887 h P t) = (term91 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139482) (@lem1139471 _26886 _26887 h P t)). Qed.
Lemma lem1139494 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term61 _26886 _26887 h P t) = (term61 _26886 _26887 h P t).
Proof. exact (eq_refl (term61 _26886 _26887 h P t)). Qed.
Lemma lem1139495 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : ((term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)) = ((term90 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)).
Proof. exact (MK_COMB (@lem1139483 _26886 _26887 h P t) (@lem1139494 _26886 _26887 h P t)). Qed.
Lemma lem1139496 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term63 _26886 _26887 h P t) = ((term90 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)).
Proof. exact (TRANS (@lem1139444 _26886 _26887 h P t) (@lem1139495 _26886 _26887 h P t)). Qed.
Lemma lem1139497 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term12 _26886 _26887 P t) = (term12 _26886 _26887 P t).
Proof. exact (eq_refl (term12 _26886 _26887 P t)). Qed.
Lemma lem1139498 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term65 _26886 _26887 h P t) = (term92 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139497 _26886 _26887 P t) (@lem1139496 _26886 _26887 h P t)). Qed.
Lemma lem1139501 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term93 _26886 _26887 P t) = (term94 _26886 _26887 P t).
Proof. exact (fun_ext (fun h : _26886 => @lem1139498 _26886 _26887 h P t)). Qed.
Lemma lem1139502 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139503 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term95 _26886 _26887 P t) = (term96 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139502 _26886) (@lem1139501 _26886 _26887 P t)). Qed.
Lemma lem1139508 {_26886 _26887 : Type'} (t : list _26886) : (term97 _26886 _26887 t) = (term98 _26886 _26887 t).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139503 _26886 _26887 P t)). Qed.
Lemma lem1139509 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1139510 {_26886 _26887 : Type'} (t : list _26886) : (term99 _26886 _26887 t) = (term100 _26886 _26887 t).
Proof. exact (MK_COMB (@lem1139509 _26886 _26887) (@lem1139508 _26886 _26887 t)). Qed.
Lemma lem1139515 {_26886 _26887 : Type'} : (term101 _26886 _26887) = (term102 _26886 _26887).
Proof. exact (fun_ext (fun t : list _26886 => @lem1139510 _26886 _26887 t)). Qed.
Lemma lem1139516 {_26886 : Type'} : (@all (list _26886)) = (@all (list _26886)).
Proof. exact (eq_refl (@all (list _26886))). Qed.
Lemma lem1139523 {_26886 _26887 : Type'} : (term103 _26886 _26887) = (term104 _26886 _26887).
Proof. exact (MK_COMB (@lem1139516 _26886) (@lem1139515 _26886 _26887)). Qed.
Lemma lem1139524 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : _18849 = (term105 _26886 _26887).
Proof. exact (h1). Qed.
Lemma lem1139525 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1139526 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (_18849 P) = (term106 _26886 _26887 P).
Proof. exact (MK_COMB (@lem1139524 _26886 _26887 _18849 h1) (@lem1139525 _26886 _26887 P)). Qed.
Lemma lem1139527 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term106 _26886 _26887 P) = (term40 _26886 _26887 P).
Proof. exact (eq_refl (term106 _26886 _26887 P)). Qed.
Lemma lem1139528 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term107 _26886 _26887 _18849 P) = (term107 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term107 _26886 _26887 _18849 P)). Qed.
Lemma lem1139529 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((_18849 P) = (term106 _26886 _26887 P)) = ((_18849 P) = (term40 _26886 _26887 P)).
Proof. exact (MK_COMB (@lem1139528 _26886 _26887 _18849 P) (@lem1139527 _26886 _26887 P)). Qed.
Lemma lem1139530 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (_18849 P) = (term40 _26886 _26887 P).
Proof. exact (EQ_MP (@lem1139529 _26886 _26887 _18849 P) (@lem1139526 _26886 _26887 P _18849 h1)). Qed.
Lemma lem1139532 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1139534 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term40 _26886 _26887 P) = (_18849 P).
Proof. exact (SYM (@lem1139530 _26886 _26887 P _18849 h1)). Qed.
Lemma lem1139535 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term40 _26886 _26887 P) = (_18849 P).
Proof. exact (@lem1139534 _26886 _26887 P _18849 h1). Qed.
Lemma lem1139536 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1139537 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term108 _26886 _26887 P) = (term109 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139536 _26886) (@lem1139535 _26886 _26887 P _18849 h1)). Qed.
Lemma lem1139538 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term10 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1139537 _26886 _26887 P _18849 h1) (@lem1139532 _26886 t)). Qed.
Lemma lem1139543 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1139544 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term75 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1139543 _26886 _26887 P x h)). Qed.
Lemma lem1139545 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139546 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term55 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139545 _26887) (@lem1139544 _26886 _26887 P h)). Qed.
Lemma lem1139547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139548 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term60 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139547) (@lem1139546 _26886 _26887 P h)). Qed.
Lemma lem1139549 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term61 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1139548 _26886 _26887 P h) (@lem1139538 _26886 _26887 P t _18849 h1)). Qed.
Lemma lem1139556 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term81 _26886 _26887 P x t)). Qed.
Lemma lem1139557 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term76 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1139556 _26886 _26887 P x t)). Qed.
Lemma lem1139558 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139559 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term9 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139558 _26887) (@lem1139557 _26886 _26887 P t)). Qed.
Lemma lem1139564 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1139565 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term75 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1139564 _26886 _26887 P x h)). Qed.
Lemma lem1139566 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139567 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term55 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139566 _26887) (@lem1139565 _26886 _26887 P h)). Qed.
Lemma lem1139568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139569 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term60 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139568) (@lem1139567 _26886 _26887 P h)). Qed.
Lemma lem1139570 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term90 _26886 _26887 h P t) = (term90 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139569 _26886 _26887 P h) (@lem1139559 _26886 _26887 P t)). Qed.
Lemma lem1139571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139572 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term91 _26886 _26887 h P t) = (term91 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139571) (@lem1139570 _26886 _26887 h P t)). Qed.
Lemma lem1139573 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : ((term90 _26886 _26887 h P t) = (term61 _26886 _26887 h P t)) = ((term90 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t)).
Proof. exact (MK_COMB (@lem1139572 _26886 _26887 h P t) (@lem1139549 _26886 _26887 h P t _18849 h1)). Qed.
Lemma lem1139574 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1139576 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term40 _26886 _26887 P) = (_18849 P).
Proof. exact (SYM (@lem1139530 _26886 _26887 P _18849 h1)). Qed.
Lemma lem1139577 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term40 _26886 _26887 P) = (_18849 P).
Proof. exact (@lem1139576 _26886 _26887 P _18849 h1). Qed.
Lemma lem1139578 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1139579 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term108 _26886 _26887 P) = (term109 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139578 _26886) (@lem1139577 _26886 _26887 P _18849 h1)). Qed.
Lemma lem1139580 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term10 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1139579 _26886 _26887 P _18849 h1) (@lem1139574 _26886 t)). Qed.
Lemma lem1139587 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term81 _26886 _26887 P x t)). Qed.
Lemma lem1139588 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term76 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1139587 _26886 _26887 P x t)). Qed.
Lemma lem1139589 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139590 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term9 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139589 _26887) (@lem1139588 _26886 _26887 P t)). Qed.
Lemma lem1139591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139592 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term112 _26886 _26887 P t) = (term112 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139591) (@lem1139590 _26886 _26887 P t)). Qed.
Lemma lem1139593 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : ((term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) = ((term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)).
Proof. exact (MK_COMB (@lem1139592 _26886 _26887 P t) (@lem1139580 _26886 _26887 P t _18849 h1)). Qed.
Lemma lem1139594 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139595 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term12 _26886 _26887 P t) = (term113 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1139594) (@lem1139593 _26886 _26887 P t _18849 h1)). Qed.
Lemma lem1139596 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term92 _26886 _26887 h P t) = (term114 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1139595 _26886 _26887 P t _18849 h1) (@lem1139573 _26886 _26887 h P t _18849 h1)). Qed.
Lemma lem1139597 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term94 _26886 _26887 P t) = (term115 _26886 _26887 _18849 P t).
Proof. exact (fun_ext (fun h : _26886 => @lem1139596 _26886 _26887 h P t _18849 h1)). Qed.
Lemma lem1139598 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139599 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term96 _26886 _26887 P t) = (term116 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1139598 _26886) (@lem1139597 _26886 _26887 P t _18849 h1)). Qed.
Lemma lem1139600 {_26886 _26887 : Type'} (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term98 _26886 _26887 t) = (term117 _26886 _26887 _18849 t).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139599 _26886 _26887 P t _18849 h1)). Qed.
Lemma lem1139601 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1139602 {_26886 _26887 : Type'} (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term100 _26886 _26887 t) = (term118 _26886 _26887 _18849 t).
Proof. exact (MK_COMB (@lem1139601 _26886 _26887) (@lem1139600 _26886 _26887 t _18849 h1)). Qed.
Lemma lem1139603 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term102 _26886 _26887) = (term119 _26886 _26887 _18849).
Proof. exact (fun_ext (fun t : list _26886 => @lem1139602 _26886 _26887 t _18849 h1)). Qed.
Lemma lem1139604 {_26886 : Type'} : (@all (list _26886)) = (@all (list _26886)).
Proof. exact (eq_refl (@all (list _26886))). Qed.
Lemma lem1139605 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (h1 : _18849 = (term105 _26886 _26887)) : (term104 _26886 _26887) = (term120 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139604 _26886) (@lem1139603 _26886 _26887 _18849 h1)). Qed.
Lemma lem1139606 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : term121 _26886 _26887 _18849.
Proof. exact (fun h0 : _18849 = (term105 _26886 _26887) => @lem1139605 _26886 _26887 _18849 h0). Qed.
Lemma lem1139607 {_26886 _26887 : Type'} : term122 _26886 _26887.
Proof. exact (fun _18849 : type740 _26886 _26887 => @lem1139606 _26886 _26887 _18849). Qed.
Lemma lem1139609 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term123 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1139610 {_26886 _26887 : Type'} (P : Prop) (c : type740 _26886 _26887) (Q : type190 _26886 _26887) : term124 _26886 _26887 P c Q.
Proof. exact (@lem1139609 (type740 _26886 _26887) P c Q). Qed.
Lemma lem1139611 {_26886 _26887 : Type'} : term125 _26886 _26887.
Proof. exact (@lem1139610 _26886 _26887 (term104 _26886 _26887) (term105 _26886 _26887) (term126 _26886 _26887)). Qed.
Lemma lem1139612 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term127 _26886 _26887 _18849) = (term120 _26886 _26887 _18849).
Proof. exact (eq_refl (term127 _26886 _26887 _18849)). Qed.
Lemma lem1139613 {_26886 _26887 : Type'} : (term128 _26886 _26887) = (term128 _26886 _26887).
Proof. exact (eq_refl (term128 _26886 _26887)). Qed.
Lemma lem1139614 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : ((term104 _26886 _26887) = (term127 _26886 _26887 _18849)) = ((term104 _26886 _26887) = (term120 _26886 _26887 _18849)).
Proof. exact (MK_COMB (@lem1139613 _26886 _26887) (@lem1139612 _26886 _26887 _18849)). Qed.
Lemma lem1139615 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term129 _26886 _26887 _18849) = (term129 _26886 _26887 _18849).
Proof. exact (eq_refl (term129 _26886 _26887 _18849)). Qed.
Lemma lem1139616 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term130 _26886 _26887 _18849) = (term121 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139615 _26886 _26887 _18849) (@lem1139614 _26886 _26887 _18849)). Qed.
Lemma lem1139617 {_26886 _26887 : Type'} : (term131 _26886 _26887) = (term132 _26886 _26887).
Proof. exact (fun_ext (fun _18849 : type740 _26886 _26887 => @lem1139616 _26886 _26887 _18849)). Qed.
Lemma lem1139618 {_26886 _26887 : Type'} : (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)) = (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)).
Proof. exact (eq_refl (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop))). Qed.
Lemma lem1139619 {_26886 _26887 : Type'} : (term133 _26886 _26887) = (term122 _26886 _26887).
Proof. exact (MK_COMB (@lem1139618 _26886 _26887) (@lem1139617 _26886 _26887)). Qed.
Lemma lem1139620 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139621 {_26886 _26887 : Type'} : (term134 _26886 _26887) = (term135 _26886 _26887).
Proof. exact (MK_COMB (@lem1139620) (@lem1139619 _26886 _26887)). Qed.
Lemma lem1139622 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term127 _26886 _26887 _18849) = (term120 _26886 _26887 _18849).
Proof. exact (eq_refl (term127 _26886 _26887 _18849)). Qed.
Lemma lem1139623 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term129 _26886 _26887 _18849) = (term129 _26886 _26887 _18849).
Proof. exact (eq_refl (term129 _26886 _26887 _18849)). Qed.
Lemma lem1139624 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term136 _26886 _26887 _18849) = (term137 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139623 _26886 _26887 _18849) (@lem1139622 _26886 _26887 _18849)). Qed.
Lemma lem1139625 {_26886 _26887 : Type'} : (term138 _26886 _26887) = (term139 _26886 _26887).
Proof. exact (fun_ext (fun _18849 : type740 _26886 _26887 => @lem1139624 _26886 _26887 _18849)). Qed.
Lemma lem1139626 {_26886 _26887 : Type'} : (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)) = (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)).
Proof. exact (eq_refl (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop))). Qed.
Lemma lem1139627 {_26886 _26887 : Type'} : (term140 _26886 _26887) = (term141 _26886 _26887).
Proof. exact (MK_COMB (@lem1139626 _26886 _26887) (@lem1139625 _26886 _26887)). Qed.
Lemma lem1139628 {_26886 _26887 : Type'} : (term128 _26886 _26887) = (term128 _26886 _26887).
Proof. exact (eq_refl (term128 _26886 _26887)). Qed.
Lemma lem1139629 {_26886 _26887 : Type'} : ((term104 _26886 _26887) = (term140 _26886 _26887)) = ((term104 _26886 _26887) = (term141 _26886 _26887)).
Proof. exact (MK_COMB (@lem1139628 _26886 _26887) (@lem1139627 _26886 _26887)). Qed.
Lemma lem1139630 {_26886 _26887 : Type'} : (term125 _26886 _26887) = (term142 _26886 _26887).
Proof. exact (MK_COMB (@lem1139621 _26886 _26887) (@lem1139629 _26886 _26887)). Qed.
Lemma lem1139631 {_26886 _26887 : Type'} : term142 _26886 _26887.
Proof. exact (EQ_MP (@lem1139630 _26886 _26887) (@lem1139611 _26886 _26887)). Qed.
Lemma lem1139632 {_26886 _26887 : Type'} : (term104 _26886 _26887) = (term141 _26886 _26887).
Proof. exact (@lem1139631 _26886 _26887 (@lem1139607 _26886 _26887)). Qed.
Lemma lem1139634 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term143 _3571 _3575 t)) = (term144 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1139635 {_26886 _26887 : Type'} (s : type740 _26886 _26887) (t : type740 _26886 _26887) : (s = (term145 _26886 _26887 t)) = (term146 _26886 _26887 s t).
Proof. exact (@lem1139634 (_26886 -> Prop) (type1470 _26886 _26887) s t). Qed.
Lemma lem1139636 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (_18849 = (term147 _26886 _26887)) = (term148 _26886 _26887 _18849).
Proof. exact (@lem1139635 _26886 _26887 _18849 (term105 _26886 _26887)). Qed.
Lemma lem1139637 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term106 _26886 _26887 P) = (term40 _26886 _26887 P).
Proof. exact (eq_refl (term106 _26886 _26887 P)). Qed.
Lemma lem1139638 {_26886 _26887 : Type'} : (term147 _26886 _26887) = (term105 _26886 _26887).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139637 _26886 _26887 P)). Qed.
Lemma lem1139639 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (@eq ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849) = (@eq ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849).
Proof. exact (eq_refl (@eq ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849)). Qed.
Lemma lem1139640 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (_18849 = (term147 _26886 _26887)) = (_18849 = (term105 _26886 _26887)).
Proof. exact (MK_COMB (@lem1139639 _26886 _26887 _18849) (@lem1139638 _26886 _26887)). Qed.
Lemma lem1139641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139642 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term149 _26886 _26887 _18849) = (term150 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139641) (@lem1139640 _26886 _26887 _18849)). Qed.
Lemma lem1139643 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term106 _26886 _26887 P) = (term40 _26886 _26887 P).
Proof. exact (eq_refl (term106 _26886 _26887 P)). Qed.
Lemma lem1139644 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term107 _26886 _26887 _18849 P) = (term107 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term107 _26886 _26887 _18849 P)). Qed.
Lemma lem1139645 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((_18849 P) = (term106 _26886 _26887 P)) = ((_18849 P) = (term40 _26886 _26887 P)).
Proof. exact (MK_COMB (@lem1139644 _26886 _26887 _18849 P) (@lem1139643 _26886 _26887 P)). Qed.
Lemma lem1139646 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term151 _26886 _26887 _18849) = (term152 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139645 _26886 _26887 _18849 P)). Qed.
Lemma lem1139647 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1139648 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term148 _26886 _26887 _18849) = (term153 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139647 _26886 _26887) (@lem1139646 _26886 _26887 _18849)). Qed.
Lemma lem1139649 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : ((_18849 = (term147 _26886 _26887)) = (term148 _26886 _26887 _18849)) = ((_18849 = (term105 _26886 _26887)) = (term153 _26886 _26887 _18849)).
Proof. exact (MK_COMB (@lem1139642 _26886 _26887 _18849) (@lem1139648 _26886 _26887 _18849)). Qed.
Lemma lem1139650 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (_18849 = (term105 _26886 _26887)) = (term153 _26886 _26887 _18849).
Proof. exact (EQ_MP (@lem1139649 _26886 _26887 _18849) (@lem1139636 _26886 _26887 _18849)). Qed.
Lemma lem1139652 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term143 _3571 _3575 t)) = (term144 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1139653 {_26886 : Type'} (s : _26886 -> Prop) (t : _26886 -> Prop) : (s = (term154 _26886 t)) = (term155 _26886 s t).
Proof. exact (@lem1139652 Prop _26886 s t). Qed.
Lemma lem1139654 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((_18849 P) = (term56 _26886 _26887 P)) = (term156 _26886 _26887 _18849 P).
Proof. exact (@lem1139653 _26886 (_18849 P) (term40 _26886 _26887 P)). Qed.
Lemma lem1139655 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term54 _26886 _26887 P s) = (term55 _26886 _26887 P s).
Proof. exact (eq_refl (term54 _26886 _26887 P s)). Qed.
Lemma lem1139656 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : (term56 _26886 _26887 P) = (term40 _26886 _26887 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139655 _26886 _26887 P s)). Qed.
Lemma lem1139657 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term107 _26886 _26887 _18849 P) = (term107 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term107 _26886 _26887 _18849 P)). Qed.
Lemma lem1139658 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((_18849 P) = (term56 _26886 _26887 P)) = ((_18849 P) = (term40 _26886 _26887 P)).
Proof. exact (MK_COMB (@lem1139657 _26886 _26887 _18849 P) (@lem1139656 _26886 _26887 P)). Qed.
Lemma lem1139659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139660 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term157 _26886 _26887 _18849 P) = (term158 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139659) (@lem1139658 _26886 _26887 _18849 P)). Qed.
Lemma lem1139661 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term54 _26886 _26887 P s) = (term55 _26886 _26887 P s).
Proof. exact (eq_refl (term54 _26886 _26887 P s)). Qed.
Lemma lem1139662 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term159 _26886 _26887 _18849 P s) = (term159 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term159 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139663 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : ((_18849 P s) = (term54 _26886 _26887 P s)) = ((_18849 P s) = (term55 _26886 _26887 P s)).
Proof. exact (MK_COMB (@lem1139662 _26886 _26887 _18849 P s) (@lem1139661 _26886 _26887 P s)). Qed.
Lemma lem1139664 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term160 _26886 _26887 _18849 P) = (term161 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139663 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139665 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139666 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term156 _26886 _26887 _18849 P) = (term162 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139665 _26886) (@lem1139664 _26886 _26887 _18849 P)). Qed.
Lemma lem1139667 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (((_18849 P) = (term56 _26886 _26887 P)) = (term156 _26886 _26887 _18849 P)) = (((_18849 P) = (term40 _26886 _26887 P)) = (term162 _26886 _26887 _18849 P)).
Proof. exact (MK_COMB (@lem1139660 _26886 _26887 _18849 P) (@lem1139666 _26886 _26887 _18849 P)). Qed.
Lemma lem1139668 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((_18849 P) = (term40 _26886 _26887 P)) = (term162 _26886 _26887 _18849 P).
Proof. exact (EQ_MP (@lem1139667 _26886 _26887 _18849 P) (@lem1139654 _26886 _26887 _18849 P)). Qed.
Lemma lem1139669 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : ((_18849 P s) = (term55 _26886 _26887 P s)) = ((_18849 P s) = (term55 _26886 _26887 P s)).
Proof. exact (eq_refl ((_18849 P s) = (term55 _26886 _26887 P s))). Qed.
Lemma lem1139670 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term161 _26886 _26887 _18849 P) = (term161 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139669 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139671 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139672 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term162 _26886 _26887 _18849 P) = (term162 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139671 _26886) (@lem1139670 _26886 _26887 _18849 P)). Qed.
Lemma lem1139673 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((_18849 P) = (term40 _26886 _26887 P)) = (term162 _26886 _26887 _18849 P).
Proof. exact (TRANS (@lem1139668 _26886 _26887 _18849 P) (@lem1139672 _26886 _26887 _18849 P)). Qed.
Lemma lem1139674 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term152 _26886 _26887 _18849) = (term163 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139673 _26886 _26887 _18849 P)). Qed.
Lemma lem1139675 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1139676 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term153 _26886 _26887 _18849) = (term164 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139675 _26886 _26887) (@lem1139674 _26886 _26887 _18849)). Qed.
Lemma lem1139677 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (_18849 = (term105 _26886 _26887)) = (term164 _26886 _26887 _18849).
Proof. exact (TRANS (@lem1139650 _26886 _26887 _18849) (@lem1139676 _26886 _26887 _18849)). Qed.
Lemma lem1139678 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139679 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term129 _26886 _26887 _18849) = (term165 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139678) (@lem1139677 _26886 _26887 _18849)). Qed.
Lemma lem1139680 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term120 _26886 _26887 _18849) = (term120 _26886 _26887 _18849).
Proof. exact (eq_refl (term120 _26886 _26887 _18849)). Qed.
Lemma lem1139681 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term137 _26886 _26887 _18849) = (term166 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139679 _26886 _26887 _18849) (@lem1139680 _26886 _26887 _18849)). Qed.
Lemma lem1139682 {_26886 _26887 : Type'} : (term139 _26886 _26887) = (term167 _26886 _26887).
Proof. exact (fun_ext (fun _18849 : type740 _26886 _26887 => @lem1139681 _26886 _26887 _18849)). Qed.
Lemma lem1139683 {_26886 _26887 : Type'} : (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)) = (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)).
Proof. exact (eq_refl (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop))). Qed.
Lemma lem1139684 {_26886 _26887 : Type'} : (term141 _26886 _26887) = (term168 _26886 _26887).
Proof. exact (MK_COMB (@lem1139683 _26886 _26887) (@lem1139682 _26886 _26887)). Qed.
Lemma lem1139685 {_26886 _26887 : Type'} : (term128 _26886 _26887) = (term128 _26886 _26887).
Proof. exact (eq_refl (term128 _26886 _26887)). Qed.
Lemma lem1139686 {_26886 _26887 : Type'} : ((term104 _26886 _26887) = (term141 _26886 _26887)) = ((term104 _26886 _26887) = (term168 _26886 _26887)).
Proof. exact (MK_COMB (@lem1139685 _26886 _26887) (@lem1139684 _26886 _26887)). Qed.
Lemma lem1139689 {_26886 _26887 : Type'} : (term104 _26886 _26887) = (term168 _26886 _26887).
Proof. exact (EQ_MP (@lem1139686 _26886 _26887) (@lem1139632 _26886 _26887)). Qed.
Lemma lem1139690 {_26886 _26887 : Type'} : (term103 _26886 _26887) = (term168 _26886 _26887).
Proof. exact (TRANS (@lem1139523 _26886 _26887) (@lem1139689 _26886 _26887)). Qed.
Lemma lem1139691 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1139692 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1139693 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term75 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1139692 _26886 _26887 P x h)). Qed.
Lemma lem1139694 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139695 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term55 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139694 _26887) (@lem1139693 _26886 _26887 P h)). Qed.
Lemma lem1139696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139697 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term60 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139696) (@lem1139695 _26886 _26887 P h)). Qed.
Lemma lem1139698 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term111 _26886 _26887 h _18849 P t) = (term111 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1139697 _26886 _26887 P h) (@lem1139691 _26886 _26887 _18849 P t)). Qed.
Lemma lem1139699 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term81 _26886 _26887 P x t)). Qed.
Lemma lem1139700 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term76 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1139699 _26886 _26887 P x t)). Qed.
Lemma lem1139701 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139702 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term9 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139701 _26887) (@lem1139700 _26886 _26887 P t)). Qed.
Lemma lem1139703 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1139704 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term75 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1139703 _26886 _26887 P x h)). Qed.
Lemma lem1139705 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139706 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term55 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139705 _26887) (@lem1139704 _26886 _26887 P h)). Qed.
Lemma lem1139707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139708 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term60 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1139707) (@lem1139706 _26886 _26887 P h)). Qed.
Lemma lem1139709 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term90 _26886 _26887 h P t) = (term90 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139708 _26886 _26887 P h) (@lem1139702 _26886 _26887 P t)). Qed.
Lemma lem1139710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139711 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term91 _26886 _26887 h P t) = (term91 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1139710) (@lem1139709 _26886 _26887 h P t)). Qed.
Lemma lem1139712 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term90 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t)) = ((term90 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t)).
Proof. exact (MK_COMB (@lem1139711 _26886 _26887 h P t) (@lem1139698 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1139713 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1139714 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term81 _26886 _26887 P x t)). Qed.
Lemma lem1139715 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term76 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1139714 _26886 _26887 P x t)). Qed.
Lemma lem1139716 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139717 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term9 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139716 _26887) (@lem1139715 _26886 _26887 P t)). Qed.
Lemma lem1139718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139719 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term112 _26886 _26887 P t) = (term112 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1139718) (@lem1139717 _26886 _26887 P t)). Qed.
Lemma lem1139720 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) = ((term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)).
Proof. exact (MK_COMB (@lem1139719 _26886 _26887 P t) (@lem1139713 _26886 _26887 _18849 P t)). Qed.
Lemma lem1139721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139722 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term113 _26886 _26887 _18849 P t) = (term113 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1139721) (@lem1139720 _26886 _26887 _18849 P t)). Qed.
Lemma lem1139723 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term114 _26886 _26887 h _18849 P t) = (term114 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1139722 _26886 _26887 _18849 P t) (@lem1139712 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1139724 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term115 _26886 _26887 _18849 P t) = (term115 _26886 _26887 _18849 P t).
Proof. exact (fun_ext (fun h : _26886 => @lem1139723 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1139725 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139726 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term116 _26886 _26887 _18849 P t) = (term116 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1139725 _26886) (@lem1139724 _26886 _26887 _18849 P t)). Qed.
Lemma lem1139727 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) : (term117 _26886 _26887 _18849 t) = (term117 _26886 _26887 _18849 t).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139726 _26886 _26887 _18849 P t)). Qed.
Lemma lem1139728 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1139729 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) : (term118 _26886 _26887 _18849 t) = (term118 _26886 _26887 _18849 t).
Proof. exact (MK_COMB (@lem1139728 _26886 _26887) (@lem1139727 _26886 _26887 _18849 t)). Qed.
Lemma lem1139730 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term119 _26886 _26887 _18849) = (term119 _26886 _26887 _18849).
Proof. exact (fun_ext (fun t : list _26886 => @lem1139729 _26886 _26887 _18849 t)). Qed.
Lemma lem1139731 {_26886 : Type'} : (@all (list _26886)) = (@all (list _26886)).
Proof. exact (eq_refl (@all (list _26886))). Qed.
Lemma lem1139732 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term120 _26886 _26887 _18849) = (term120 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139731 _26886) (@lem1139730 _26886 _26887 _18849)). Qed.
Lemma lem1139733 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (P x s) = (P x s).
Proof. exact (eq_refl (P x s)). Qed.
Lemma lem1139734 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term75 _26886 _26887 P s) = (term75 _26886 _26887 P s).
Proof. exact (fun_ext (fun x : _26887 => @lem1139733 _26886 _26887 P x s)). Qed.
Lemma lem1139735 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139736 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term55 _26886 _26887 P s) = (term55 _26886 _26887 P s).
Proof. exact (MK_COMB (@lem1139735 _26887) (@lem1139734 _26886 _26887 P s)). Qed.
Lemma lem1139739 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term159 _26886 _26887 _18849 P s) = (term159 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term159 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139740 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : ((_18849 P s) = (term55 _26886 _26887 P s)) = ((_18849 P s) = (term55 _26886 _26887 P s)).
Proof. exact (MK_COMB (@lem1139739 _26886 _26887 _18849 P s) (@lem1139736 _26886 _26887 P s)). Qed.
Lemma lem1139741 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term161 _26886 _26887 _18849 P) = (term161 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139740 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139742 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139743 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term162 _26886 _26887 _18849 P) = (term162 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139742 _26886) (@lem1139741 _26886 _26887 _18849 P)). Qed.
Lemma lem1139744 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term163 _26886 _26887 _18849) = (term163 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139743 _26886 _26887 _18849 P)). Qed.
Lemma lem1139745 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1139746 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term164 _26886 _26887 _18849) = (term164 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139745 _26886 _26887) (@lem1139744 _26886 _26887 _18849)). Qed.
Lemma lem1139747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139748 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term165 _26886 _26887 _18849) = (term165 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139747) (@lem1139746 _26886 _26887 _18849)). Qed.
Lemma lem1139749 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term166 _26886 _26887 _18849) = (term166 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139748 _26886 _26887 _18849) (@lem1139732 _26886 _26887 _18849)). Qed.
Lemma lem1139750 {_26886 _26887 : Type'} : (term167 _26886 _26887) = (term167 _26886 _26887).
Proof. exact (fun_ext (fun _18849 : type740 _26886 _26887 => @lem1139749 _26886 _26887 _18849)). Qed.
Lemma lem1139751 {_26886 _26887 : Type'} : (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)) = (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop)).
Proof. exact (eq_refl (@all ((_26887 -> _26886 -> Prop) -> _26886 -> Prop))). Qed.
Lemma lem1139752 {_26886 _26887 : Type'} : (term168 _26886 _26887) = (term168 _26886 _26887).
Proof. exact (MK_COMB (@lem1139751 _26886 _26887) (@lem1139750 _26886 _26887)). Qed.
Lemma lem1139829 {_26886 _26887 : Type'} : (term103 _26886 _26887) = (term168 _26886 _26887).
Proof. exact (TRANS (@lem1139690 _26886 _26887) (@lem1139752 _26886 _26887)). Qed.
Lemma lem1139830 {_26886 _26887 : Type'} : (term168 _26886 _26887) = (term103 _26886 _26887).
Proof. exact (SYM (@lem1139829 _26886 _26887)). Qed.
Lemma lem1139831 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (h1 : term164 _26886 _26887 _18849) : term164 _26886 _26887 _18849.
Proof. exact (h1). Qed.
Lemma lem1139832 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (h1). Qed.
Lemma lem1139834 (p : Prop) : p = (term62 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1139835 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term90 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t)) = (term169 _26886 _26887 h _18849 P t).
Proof. exact (@lem1139834 ((term90 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t))). Qed.
Lemma lem1139836 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term169 _26886 _26887 h _18849 P t) = ((term90 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t)).
Proof. exact (SYM (@lem1139835 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1139837 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term170 _26886 _26887 h _18849 P t) : term170 _26886 _26887 h _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1139841 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (P x s) = (P x s).
Proof. exact (eq_refl (P x s)). Qed.
Lemma lem1139842 {_26887 : Type'} (P : _26887 -> Prop) : (term171 _26887 P) = (term172 _26887 P).
Proof. exact (@lem18394 _26887 P). Qed.
Lemma lem1139843 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term173 _26886 _26887 P s) = (term174 _26886 _26887 P s).
Proof. exact (@lem1139842 _26887 (term75 _26886 _26887 P s)). Qed.
Lemma lem1139844 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (term77 _26886 _26887 P s x) = (P x s).
Proof. exact (eq_refl (term77 _26886 _26887 P s x)). Qed.
Lemma lem1139845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1139847 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (term175 _26886 _26887 P s x) = (term176 _26886 _26887 P x s).
Proof. exact (MK_COMB (@lem1139845) (@lem1139844 _26886 _26887 P x s)). Qed.
Lemma lem1139848 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term177 _26886 _26887 P s) = (term178 _26886 _26887 P s).
Proof. exact (fun_ext (fun x : _26887 => @lem1139847 _26886 _26887 P x s)). Qed.
Lemma lem1139849 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1139850 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term174 _26886 _26887 P s) = (term179 _26886 _26887 P s).
Proof. exact (MK_COMB (@lem1139849 _26887) (@lem1139848 _26886 _26887 P s)). Qed.
Lemma lem1139851 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term173 _26886 _26887 P s) = (term179 _26886 _26887 P s).
Proof. exact (TRANS (@lem1139843 _26886 _26887 P s) (@lem1139850 _26886 _26887 P s)). Qed.
Lemma lem1139852 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term75 _26886 _26887 P s) = (term75 _26886 _26887 P s).
Proof. exact (fun_ext (fun x : _26887 => @lem1139841 _26886 _26887 P x s)). Qed.
Lemma lem1139853 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1139854 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term55 _26886 _26887 P s) = (term55 _26886 _26887 P s).
Proof. exact (MK_COMB (@lem1139853 _26887) (@lem1139852 _26886 _26887 P s)). Qed.
Lemma lem1139856 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term180 _26886 _26887 _18849 P s) = (term180 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term180 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139857 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term181 _26886 _26887 _18849 P s) = (term181 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1139856 _26886 _26887 _18849 P s) (@lem1139854 _26886 _26887 P s)). Qed.
Lemma lem1139859 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term182 _26886 _26887 _18849 P s) = (term182 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term182 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139860 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term183 _26886 _26887 _18849 P s) = (term184 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1139859 _26886 _26887 _18849 P s) (@lem1139851 _26886 _26887 P s)). Qed.
Lemma lem1139861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1139862 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term185 _26886 _26887 _18849 P s) = (term186 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1139861) (@lem1139860 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139863 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term187 _26886 _26887 _18849 P s) = (term188 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1139862 _26886 _26887 _18849 P s) (@lem1139857 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139864 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : ((_18849 P s) = (term55 _26886 _26887 P s)) = (term187 _26886 _26887 _18849 P s).
Proof. exact (@lem17784 (_18849 P s) (term55 _26886 _26887 P s)). Qed.
Lemma lem1139865 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : ((_18849 P s) = (term55 _26886 _26887 P s)) = (term188 _26886 _26887 _18849 P s).
Proof. exact (TRANS (@lem1139864 _26886 _26887 _18849 P s) (@lem1139863 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139866 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term161 _26886 _26887 _18849 P) = (term189 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139865 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139867 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139868 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term162 _26886 _26887 _18849 P) = (term190 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139867 _26886) (@lem1139866 _26886 _26887 _18849 P)). Qed.
Lemma lem1139869 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term163 _26886 _26887 _18849) = (term191 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139868 _26886 _26887 _18849 P)). Qed.
Lemma lem1139870 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1139871 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term164 _26886 _26887 _18849) = (term192 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1139870 _26886 _26887) (@lem1139869 _26886 _26887 _18849)). Qed.
Lemma lem1139877 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1139878 {_26886 : Type'} (P : _26886 -> Prop) (Q : _26886 -> Prop) : (term193 _26886 P Q) = (term194 _26886 P Q).
Proof. exact (@lem1139877 _26886 P Q). Qed.
Lemma lem1139879 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term195 _26886 _26887 _18849 P) = (term196 _26886 _26887 _18849 P).
Proof. exact (@lem1139878 _26886 (term197 _26886 _26887 _18849 P) (term198 _26886 _26887 _18849 P)). Qed.
Lemma lem1139880 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term199 _26886 _26887 _18849 P s) = (term184 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term199 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1139882 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term200 _26886 _26887 _18849 P s) = (term186 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1139881) (@lem1139880 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139883 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term201 _26886 _26887 _18849 P s) = (term181 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term201 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139884 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term202 _26886 _26887 _18849 P s) = (term188 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1139882 _26886 _26887 _18849 P s) (@lem1139883 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139885 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term203 _26886 _26887 _18849 P) = (term189 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139884 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139886 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139887 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term195 _26886 _26887 _18849 P) = (term190 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139886 _26886) (@lem1139885 _26886 _26887 _18849 P)). Qed.
Lemma lem1139888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139889 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term204 _26886 _26887 _18849 P) = (term205 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139888) (@lem1139887 _26886 _26887 _18849 P)). Qed.
Lemma lem1139890 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term199 _26886 _26887 _18849 P s) = (term184 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term199 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139891 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term206 _26886 _26887 _18849 P) = (term197 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139890 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139892 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139893 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term207 _26886 _26887 _18849 P) = (term208 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139892 _26886) (@lem1139891 _26886 _26887 _18849 P)). Qed.
Lemma lem1139894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1139895 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term209 _26886 _26887 _18849 P) = (term210 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139894) (@lem1139893 _26886 _26887 _18849 P)). Qed.
Lemma lem1139896 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term201 _26886 _26887 _18849 P s) = (term181 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term201 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139897 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term211 _26886 _26887 _18849 P) = (term198 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1139896 _26886 _26887 _18849 P s)). Qed.
Lemma lem1139898 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1139899 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term212 _26886 _26887 _18849 P) = (term213 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139898 _26886) (@lem1139897 _26886 _26887 _18849 P)). Qed.
Lemma lem1139900 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term196 _26886 _26887 _18849 P) = (term214 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1139895 _26886 _26887 _18849 P) (@lem1139899 _26886 _26887 _18849 P)). Qed.
Lemma lem1139901 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((term195 _26886 _26887 _18849 P) = (term196 _26886 _26887 _18849 P)) = ((term190 _26886 _26887 _18849 P) = (term214 _26886 _26887 _18849 P)).
Proof. exact (MK_COMB (@lem1139889 _26886 _26887 _18849 P) (@lem1139900 _26886 _26887 _18849 P)). Qed.
Lemma lem1139902 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term190 _26886 _26887 _18849 P) = (term214 _26886 _26887 _18849 P).
Proof. exact (EQ_MP (@lem1139901 _26886 _26887 _18849 P) (@lem1139879 _26886 _26887 _18849 P)). Qed.
Lemma lem1140007 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term191 _26886 _26887 _18849) = (term215 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1139902 _26886 _26887 _18849 P)). Qed.
Lemma lem1140008 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1140009 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term192 _26886 _26887 _18849) = (term216 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140008 _26886 _26887) (@lem1140007 _26886 _26887 _18849)). Qed.
Lemma lem1140011 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1140012 {_26886 _26887 : Type'} (P : type745 _26886 _26887) (Q : type745 _26886 _26887) : (term217 _26886 _26887 P Q) = (term218 _26886 _26887 P Q).
Proof. exact (@lem1140011 (type1470 _26886 _26887) P Q). Qed.
Lemma lem1140013 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term219 _26886 _26887 _18849) = (term220 _26886 _26887 _18849).
Proof. exact (@lem1140012 _26886 _26887 (term221 _26886 _26887 _18849) (term222 _26886 _26887 _18849)). Qed.
Lemma lem1140014 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term223 _26886 _26887 _18849 P) = (term208 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term223 _26886 _26887 _18849 P)). Qed.
Lemma lem1140015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140016 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term224 _26886 _26887 _18849 P) = (term210 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140015) (@lem1140014 _26886 _26887 _18849 P)). Qed.
Lemma lem1140017 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term225 _26886 _26887 _18849 P) = (term213 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term225 _26886 _26887 _18849 P)). Qed.
Lemma lem1140018 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term226 _26886 _26887 _18849 P) = (term214 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140016 _26886 _26887 _18849 P) (@lem1140017 _26886 _26887 _18849 P)). Qed.
Lemma lem1140019 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term227 _26886 _26887 _18849) = (term215 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1140018 _26886 _26887 _18849 P)). Qed.
Lemma lem1140020 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1140021 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term219 _26886 _26887 _18849) = (term216 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140020 _26886 _26887) (@lem1140019 _26886 _26887 _18849)). Qed.
Lemma lem1140022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140023 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term228 _26886 _26887 _18849) = (term229 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140022) (@lem1140021 _26886 _26887 _18849)). Qed.
Lemma lem1140024 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term223 _26886 _26887 _18849 P) = (term208 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term223 _26886 _26887 _18849 P)). Qed.
Lemma lem1140025 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term230 _26886 _26887 _18849) = (term221 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1140024 _26886 _26887 _18849 P)). Qed.
Lemma lem1140026 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1140027 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term231 _26886 _26887 _18849) = (term232 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140026 _26886 _26887) (@lem1140025 _26886 _26887 _18849)). Qed.
Lemma lem1140028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140029 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term233 _26886 _26887 _18849) = (term234 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140028) (@lem1140027 _26886 _26887 _18849)). Qed.
Lemma lem1140030 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term225 _26886 _26887 _18849 P) = (term213 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term225 _26886 _26887 _18849 P)). Qed.
Lemma lem1140031 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term235 _26886 _26887 _18849) = (term222 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1140030 _26886 _26887 _18849 P)). Qed.
Lemma lem1140032 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1140033 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term236 _26886 _26887 _18849) = (term237 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140032 _26886 _26887) (@lem1140031 _26886 _26887 _18849)). Qed.
Lemma lem1140034 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term220 _26886 _26887 _18849) = (term238 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140029 _26886 _26887 _18849) (@lem1140033 _26886 _26887 _18849)). Qed.
Lemma lem1140035 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : ((term219 _26886 _26887 _18849) = (term220 _26886 _26887 _18849)) = ((term216 _26886 _26887 _18849) = (term238 _26886 _26887 _18849)).
Proof. exact (MK_COMB (@lem1140023 _26886 _26887 _18849) (@lem1140034 _26886 _26887 _18849)). Qed.
Lemma lem1140036 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term216 _26886 _26887 _18849) = (term238 _26886 _26887 _18849).
Proof. exact (EQ_MP (@lem1140035 _26886 _26887 _18849) (@lem1140013 _26886 _26887 _18849)). Qed.
Lemma lem1140149 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term192 _26886 _26887 _18849) = (term238 _26886 _26887 _18849).
Proof. exact (TRANS (@lem1140009 _26886 _26887 _18849) (@lem1140036 _26886 _26887 _18849)). Qed.
Lemma lem1140151 {A : Type'} (P : Prop) (Q : A -> Prop) : (term239 A P Q) = (term240 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1140152 {_26887 : Type'} (P : Prop) (Q : _26887 -> Prop) : (term239 _26887 P Q) = (term240 _26887 P Q).
Proof. exact (@lem1140151 _26887 P Q). Qed.
Lemma lem1140153 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term241 _26886 _26887 _18849 P s) = (term242 _26886 _26887 _18849 P s).
Proof. exact (@lem1140152 _26887 (term243 _26886 _26887 _18849 P s) (term75 _26886 _26887 P s)). Qed.
Lemma lem1140154 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (term77 _26886 _26887 P s x) = (P x s).
Proof. exact (eq_refl (term77 _26886 _26887 P s x)). Qed.
Lemma lem1140155 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term85 _26886 _26887 P s) = (term75 _26886 _26887 P s).
Proof. exact (fun_ext (fun x : _26887 => @lem1140154 _26886 _26887 P x s)). Qed.
Lemma lem1140156 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140157 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (s : _26886) : (term86 _26886 _26887 P s) = (term55 _26886 _26887 P s).
Proof. exact (MK_COMB (@lem1140156 _26887) (@lem1140155 _26886 _26887 P s)). Qed.
Lemma lem1140158 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term180 _26886 _26887 _18849 P s) = (term180 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term180 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140159 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term241 _26886 _26887 _18849 P s) = (term181 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1140158 _26886 _26887 _18849 P s) (@lem1140157 _26886 _26887 P s)). Qed.
Lemma lem1140160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140161 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term244 _26886 _26887 _18849 P s) = (term245 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1140160) (@lem1140159 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140162 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (term77 _26886 _26887 P s x) = (P x s).
Proof. exact (eq_refl (term77 _26886 _26887 P s x)). Qed.
Lemma lem1140163 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term180 _26886 _26887 _18849 P s) = (term180 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term180 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140164 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (term246 _26886 _26887 _18849 P s x) = (term247 _26886 _26887 _18849 P x s).
Proof. exact (MK_COMB (@lem1140163 _26886 _26887 _18849 P s) (@lem1140162 _26886 _26887 P x s)). Qed.
Lemma lem1140165 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term248 _26886 _26887 _18849 P s) = (term249 _26886 _26887 _18849 P s).
Proof. exact (fun_ext (fun x : _26887 => @lem1140164 _26886 _26887 _18849 P x s)). Qed.
Lemma lem1140166 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140167 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term242 _26886 _26887 _18849 P s) = (term250 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1140166 _26887) (@lem1140165 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140168 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : ((term241 _26886 _26887 _18849 P s) = (term242 _26886 _26887 _18849 P s)) = ((term181 _26886 _26887 _18849 P s) = (term250 _26886 _26887 _18849 P s)).
Proof. exact (MK_COMB (@lem1140161 _26886 _26887 _18849 P s) (@lem1140167 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140169 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term181 _26886 _26887 _18849 P s) = (term250 _26886 _26887 _18849 P s).
Proof. exact (EQ_MP (@lem1140168 _26886 _26887 _18849 P s) (@lem1140153 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140170 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term198 _26886 _26887 _18849 P) = (term251 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1140169 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140171 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1140172 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term213 _26886 _26887 _18849 P) = (term252 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140171 _26886) (@lem1140170 _26886 _26887 _18849 P)). Qed.
Lemma lem1140174 {A B : Type'} (P : type1413 A B) : (term253 A B P) = (term254 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1140175 {_26886 _26887 : Type'} (P : type1413 _26886 _26887) : (term253 _26886 _26887 P) = (term254 _26886 _26887 P).
Proof. exact (@lem1140174 _26886 _26887 P). Qed.
Lemma lem1140176 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term255 _26886 _26887 _18849 P) = (term256 _26886 _26887 _18849 P).
Proof. exact (@lem1140175 _26886 _26887 (term257 _26886 _26887 _18849 P)). Qed.
Lemma lem1140177 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term258 _26886 _26887 _18849 P s) = (term249 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term258 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140178 {_26887 : Type'} (x : _26887) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1140179 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) (x : _26887) : (term259 _26886 _26887 _18849 P s x) = (term260 _26886 _26887 _18849 P s x).
Proof. exact (MK_COMB (@lem1140177 _26886 _26887 _18849 P s) (@lem1140178 _26887 x)). Qed.
Lemma lem1140180 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (term260 _26886 _26887 _18849 P s x) = (term247 _26886 _26887 _18849 P x s).
Proof. exact (eq_refl (term260 _26886 _26887 _18849 P s x)). Qed.
Lemma lem1140181 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (s : _26886) : (term259 _26886 _26887 _18849 P s x) = (term247 _26886 _26887 _18849 P x s).
Proof. exact (TRANS (@lem1140179 _26886 _26887 _18849 P s x) (@lem1140180 _26886 _26887 _18849 P x s)). Qed.
Lemma lem1140182 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term261 _26886 _26887 _18849 P s) = (term249 _26886 _26887 _18849 P s).
Proof. exact (fun_ext (fun x : _26887 => @lem1140181 _26886 _26887 _18849 P x s)). Qed.
Lemma lem1140183 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140184 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term262 _26886 _26887 _18849 P s) = (term250 _26886 _26887 _18849 P s).
Proof. exact (MK_COMB (@lem1140183 _26887) (@lem1140182 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140185 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term263 _26886 _26887 _18849 P) = (term251 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun s : _26886 => @lem1140184 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140186 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1140187 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term255 _26886 _26887 _18849 P) = (term252 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140186 _26886) (@lem1140185 _26886 _26887 _18849 P)). Qed.
Lemma lem1140188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140189 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term264 _26886 _26887 _18849 P) = (term265 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140188) (@lem1140187 _26886 _26887 _18849 P)). Qed.
Lemma lem1140190 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (s : _26886) : (term258 _26886 _26887 _18849 P s) = (term249 _26886 _26887 _18849 P s).
Proof. exact (eq_refl (term258 _26886 _26887 _18849 P s)). Qed.
Lemma lem1140191 {_26886 _26887 : Type'} (x : _26886 -> _26887) (s : _26886) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem1140192 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) (s : _26886) : (term266 _26886 _26887 _18849 P x s) = (term267 _26886 _26887 _18849 P x s).
Proof. exact (MK_COMB (@lem1140190 _26886 _26887 _18849 P s) (@lem1140191 _26886 _26887 x s)). Qed.
Lemma lem1140193 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) (s : _26886) : (term267 _26886 _26887 _18849 P x s) = (term268 _26886 _26887 _18849 P x s).
Proof. exact (eq_refl (term267 _26886 _26887 _18849 P x s)). Qed.
Lemma lem1140194 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) (s : _26886) : (term266 _26886 _26887 _18849 P x s) = (term268 _26886 _26887 _18849 P x s).
Proof. exact (TRANS (@lem1140192 _26886 _26887 _18849 P x s) (@lem1140193 _26886 _26887 _18849 P x s)). Qed.
Lemma lem1140195 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) : (term269 _26886 _26887 _18849 P x) = (term270 _26886 _26887 _18849 P x).
Proof. exact (fun_ext (fun s : _26886 => @lem1140194 _26886 _26887 _18849 P x s)). Qed.
Lemma lem1140196 {_26886 : Type'} : (@all _26886) = (@all _26886).
Proof. exact (eq_refl (@all _26886)). Qed.
Lemma lem1140197 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) : (term271 _26886 _26887 _18849 P x) = (term272 _26886 _26887 _18849 P x).
Proof. exact (MK_COMB (@lem1140196 _26886) (@lem1140195 _26886 _26887 _18849 P x)). Qed.
Lemma lem1140198 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term273 _26886 _26887 _18849 P) = (term274 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun x : _26886 -> _26887 => @lem1140197 _26886 _26887 _18849 P x)). Qed.
Lemma lem1140199 {_26886 _26887 : Type'} : (@ex (_26886 -> _26887)) = (@ex (_26886 -> _26887)).
Proof. exact (eq_refl (@ex (_26886 -> _26887))). Qed.
Lemma lem1140200 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term256 _26886 _26887 _18849 P) = (term275 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140199 _26886 _26887) (@lem1140198 _26886 _26887 _18849 P)). Qed.
Lemma lem1140201 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : ((term255 _26886 _26887 _18849 P) = (term256 _26886 _26887 _18849 P)) = ((term252 _26886 _26887 _18849 P) = (term275 _26886 _26887 _18849 P)).
Proof. exact (MK_COMB (@lem1140189 _26886 _26887 _18849 P) (@lem1140200 _26886 _26887 _18849 P)). Qed.
Lemma lem1140202 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term252 _26886 _26887 _18849 P) = (term275 _26886 _26887 _18849 P).
Proof. exact (EQ_MP (@lem1140201 _26886 _26887 _18849 P) (@lem1140176 _26886 _26887 _18849 P)). Qed.
Lemma lem1140203 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term213 _26886 _26887 _18849 P) = (term275 _26886 _26887 _18849 P).
Proof. exact (TRANS (@lem1140172 _26886 _26887 _18849 P) (@lem1140202 _26886 _26887 _18849 P)). Qed.
Lemma lem1140204 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term222 _26886 _26887 _18849) = (term276 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1140203 _26886 _26887 _18849 P)). Qed.
Lemma lem1140205 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1140206 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term237 _26886 _26887 _18849) = (term277 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140205 _26886 _26887) (@lem1140204 _26886 _26887 _18849)). Qed.
Lemma lem1140208 {A B : Type'} (P : type1413 A B) : (term253 A B P) = (term254 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1140209 {_26886 _26887 : Type'} (P : type730 _26886 _26887) : (term278 _26886 _26887 P) = (term279 _26886 _26887 P).
Proof. exact (@lem1140208 (type1470 _26886 _26887) (_26886 -> _26887) P). Qed.
Lemma lem1140210 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term280 _26886 _26887 _18849) = (term281 _26886 _26887 _18849).
Proof. exact (@lem1140209 _26886 _26887 (term282 _26886 _26887 _18849)). Qed.
Lemma lem1140211 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term283 _26886 _26887 _18849 P) = (term274 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term283 _26886 _26887 _18849 P)). Qed.
Lemma lem1140212 {_26886 _26887 : Type'} (x : _26886 -> _26887) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1140213 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) : (term284 _26886 _26887 _18849 P x) = (term285 _26886 _26887 _18849 P x).
Proof. exact (MK_COMB (@lem1140211 _26886 _26887 _18849 P) (@lem1140212 _26886 _26887 x)). Qed.
Lemma lem1140214 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) : (term285 _26886 _26887 _18849 P x) = (term272 _26886 _26887 _18849 P x).
Proof. exact (eq_refl (term285 _26886 _26887 _18849 P x)). Qed.
Lemma lem1140215 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26886 -> _26887) : (term284 _26886 _26887 _18849 P x) = (term272 _26886 _26887 _18849 P x).
Proof. exact (TRANS (@lem1140213 _26886 _26887 _18849 P x) (@lem1140214 _26886 _26887 _18849 P x)). Qed.
Lemma lem1140216 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term286 _26886 _26887 _18849 P) = (term274 _26886 _26887 _18849 P).
Proof. exact (fun_ext (fun x : _26886 -> _26887 => @lem1140215 _26886 _26887 _18849 P x)). Qed.
Lemma lem1140217 {_26886 _26887 : Type'} : (@ex (_26886 -> _26887)) = (@ex (_26886 -> _26887)).
Proof. exact (eq_refl (@ex (_26886 -> _26887))). Qed.
Lemma lem1140218 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term287 _26886 _26887 _18849 P) = (term275 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140217 _26886 _26887) (@lem1140216 _26886 _26887 _18849 P)). Qed.
Lemma lem1140219 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term288 _26886 _26887 _18849) = (term276 _26886 _26887 _18849).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1140218 _26886 _26887 _18849 P)). Qed.
Lemma lem1140220 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1140221 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term280 _26886 _26887 _18849) = (term277 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140220 _26886 _26887) (@lem1140219 _26886 _26887 _18849)). Qed.
Lemma lem1140222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140223 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term289 _26886 _26887 _18849) = (term290 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140222) (@lem1140221 _26886 _26887 _18849)). Qed.
Lemma lem1140224 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term283 _26886 _26887 _18849 P) = (term274 _26886 _26887 _18849 P).
Proof. exact (eq_refl (term283 _26886 _26887 _18849 P)). Qed.
Lemma lem1140225 {_26886 _26887 : Type'} (x : type739 _26886 _26887) (P : type1470 _26886 _26887) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem1140226 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) (P : type1470 _26886 _26887) : (term291 _26886 _26887 _18849 x P) = (term292 _26886 _26887 _18849 x P).
Proof. exact (MK_COMB (@lem1140224 _26886 _26887 _18849 P) (@lem1140225 _26886 _26887 x P)). Qed.
Lemma lem1140227 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) (P : type1470 _26886 _26887) : (term292 _26886 _26887 _18849 x P) = (term293 _26886 _26887 _18849 x P).
Proof. exact (eq_refl (term292 _26886 _26887 _18849 x P)). Qed.
Lemma lem1140228 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) (P : type1470 _26886 _26887) : (term291 _26886 _26887 _18849 x P) = (term293 _26886 _26887 _18849 x P).
Proof. exact (TRANS (@lem1140226 _26886 _26887 _18849 x P) (@lem1140227 _26886 _26887 _18849 x P)). Qed.
Lemma lem1140229 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) : (term294 _26886 _26887 _18849 x) = (term295 _26886 _26887 _18849 x).
Proof. exact (fun_ext (fun P : type1470 _26886 _26887 => @lem1140228 _26886 _26887 _18849 x P)). Qed.
Lemma lem1140230 {_26886 _26887 : Type'} : (@all (_26887 -> _26886 -> Prop)) = (@all (_26887 -> _26886 -> Prop)).
Proof. exact (eq_refl (@all (_26887 -> _26886 -> Prop))). Qed.
Lemma lem1140231 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) : (term296 _26886 _26887 _18849 x) = (term297 _26886 _26887 _18849 x).
Proof. exact (MK_COMB (@lem1140230 _26886 _26887) (@lem1140229 _26886 _26887 _18849 x)). Qed.
Lemma lem1140232 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term298 _26886 _26887 _18849) = (term299 _26886 _26887 _18849).
Proof. exact (fun_ext (fun x : type739 _26886 _26887 => @lem1140231 _26886 _26887 _18849 x)). Qed.
Lemma lem1140233 {_26886 _26887 : Type'} : (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887)) = (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887)).
Proof. exact (eq_refl (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887))). Qed.
Lemma lem1140234 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term281 _26886 _26887 _18849) = (term300 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140233 _26886 _26887) (@lem1140232 _26886 _26887 _18849)). Qed.
Lemma lem1140235 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : ((term280 _26886 _26887 _18849) = (term281 _26886 _26887 _18849)) = ((term277 _26886 _26887 _18849) = (term300 _26886 _26887 _18849)).
Proof. exact (MK_COMB (@lem1140223 _26886 _26887 _18849) (@lem1140234 _26886 _26887 _18849)). Qed.
Lemma lem1140236 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term277 _26886 _26887 _18849) = (term300 _26886 _26887 _18849).
Proof. exact (EQ_MP (@lem1140235 _26886 _26887 _18849) (@lem1140210 _26886 _26887 _18849)). Qed.
Lemma lem1140237 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term237 _26886 _26887 _18849) = (term300 _26886 _26887 _18849).
Proof. exact (TRANS (@lem1140206 _26886 _26887 _18849) (@lem1140236 _26886 _26887 _18849)). Qed.
Lemma lem1140238 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term234 _26886 _26887 _18849) = (term234 _26886 _26887 _18849).
Proof. exact (eq_refl (term234 _26886 _26887 _18849)). Qed.
Lemma lem1140239 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term238 _26886 _26887 _18849) = (term301 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140238 _26886 _26887 _18849) (@lem1140237 _26886 _26887 _18849)). Qed.
Lemma lem1140241 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1140242 {_26886 _26887 : Type'} (P : Prop) (Q : type189 _26886 _26887) : (term304 _26886 _26887 P Q) = (term305 _26886 _26887 P Q).
Proof. exact (@lem1140241 (type739 _26886 _26887) P Q). Qed.
Lemma lem1140243 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term306 _26886 _26887 _18849) = (term307 _26886 _26887 _18849).
Proof. exact (@lem1140242 _26886 _26887 (term232 _26886 _26887 _18849) (term299 _26886 _26887 _18849)). Qed.
Lemma lem1140244 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) : (term308 _26886 _26887 _18849 x) = (term297 _26886 _26887 _18849 x).
Proof. exact (eq_refl (term308 _26886 _26887 _18849 x)). Qed.
Lemma lem1140245 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term309 _26886 _26887 _18849) = (term299 _26886 _26887 _18849).
Proof. exact (fun_ext (fun x : type739 _26886 _26887 => @lem1140244 _26886 _26887 _18849 x)). Qed.
Lemma lem1140246 {_26886 _26887 : Type'} : (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887)) = (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887)).
Proof. exact (eq_refl (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887))). Qed.
Lemma lem1140247 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term310 _26886 _26887 _18849) = (term300 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140246 _26886 _26887) (@lem1140245 _26886 _26887 _18849)). Qed.
Lemma lem1140248 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term234 _26886 _26887 _18849) = (term234 _26886 _26887 _18849).
Proof. exact (eq_refl (term234 _26886 _26887 _18849)). Qed.
Lemma lem1140249 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term306 _26886 _26887 _18849) = (term301 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140248 _26886 _26887 _18849) (@lem1140247 _26886 _26887 _18849)). Qed.
Lemma lem1140250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140251 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term311 _26886 _26887 _18849) = (term312 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140250) (@lem1140249 _26886 _26887 _18849)). Qed.
Lemma lem1140252 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) : (term308 _26886 _26887 _18849 x) = (term297 _26886 _26887 _18849 x).
Proof. exact (eq_refl (term308 _26886 _26887 _18849 x)). Qed.
Lemma lem1140253 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term234 _26886 _26887 _18849) = (term234 _26886 _26887 _18849).
Proof. exact (eq_refl (term234 _26886 _26887 _18849)). Qed.
Lemma lem1140254 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (x : type739 _26886 _26887) : (term313 _26886 _26887 _18849 x) = (term314 _26886 _26887 _18849 x).
Proof. exact (MK_COMB (@lem1140253 _26886 _26887 _18849) (@lem1140252 _26886 _26887 _18849 x)). Qed.
Lemma lem1140255 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term315 _26886 _26887 _18849) = (term316 _26886 _26887 _18849).
Proof. exact (fun_ext (fun x : type739 _26886 _26887 => @lem1140254 _26886 _26887 _18849 x)). Qed.
Lemma lem1140256 {_26886 _26887 : Type'} : (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887)) = (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887)).
Proof. exact (eq_refl (@ex ((_26887 -> _26886 -> Prop) -> _26886 -> _26887))). Qed.
Lemma lem1140257 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term307 _26886 _26887 _18849) = (term317 _26886 _26887 _18849).
Proof. exact (MK_COMB (@lem1140256 _26886 _26887) (@lem1140255 _26886 _26887 _18849)). Qed.
Lemma lem1140258 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : ((term306 _26886 _26887 _18849) = (term307 _26886 _26887 _18849)) = ((term301 _26886 _26887 _18849) = (term317 _26886 _26887 _18849)).
Proof. exact (MK_COMB (@lem1140251 _26886 _26887 _18849) (@lem1140257 _26886 _26887 _18849)). Qed.
Lemma lem1140259 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term301 _26886 _26887 _18849) = (term317 _26886 _26887 _18849).
Proof. exact (EQ_MP (@lem1140258 _26886 _26887 _18849) (@lem1140243 _26886 _26887 _18849)). Qed.
Lemma lem1140260 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term238 _26886 _26887 _18849) = (term317 _26886 _26887 _18849).
Proof. exact (TRANS (@lem1140239 _26886 _26887 _18849) (@lem1140259 _26886 _26887 _18849)). Qed.
Lemma lem1140261 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term192 _26886 _26887 _18849) = (term317 _26886 _26887 _18849).
Proof. exact (TRANS (@lem1140149 _26886 _26887 _18849) (@lem1140260 _26886 _26887 _18849)). Qed.
Lemma lem1140262 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : (term164 _26886 _26887 _18849) = (term317 _26886 _26887 _18849).
Proof. exact (TRANS (@lem1139871 _26886 _26887 _18849) (@lem1140261 _26886 _26887 _18849)). Qed.
Lemma lem1140263 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (h1 : term164 _26886 _26887 _18849) : term317 _26886 _26887 _18849.
Proof. exact (EQ_MP (@lem1140262 _26886 _26887 _18849) (@lem1139831 _26886 _26887 _18849 h1)). Qed.
Lemma lem1140265 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term81 _26886 _26887 P x t)). Qed.
Lemma lem1140266 {_26887 : Type'} (P : _26887 -> Prop) : (term171 _26887 P) = (term172 _26887 P).
Proof. exact (@lem18394 _26887 P). Qed.
Lemma lem1140267 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term318 _26886 _26887 P t) = (term319 _26886 _26887 P t).
Proof. exact (@lem1140266 _26887 (term76 _26886 _26887 P t)). Qed.
Lemma lem1140268 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1140269 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140271 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term320 _26886 _26887 P t x) = (term321 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140269) (@lem1140268 _26886 _26887 P x t)). Qed.
Lemma lem1140272 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term322 _26886 _26887 P t) = (term323 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140271 _26886 _26887 P x t)). Qed.
Lemma lem1140273 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140274 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term319 _26886 _26887 P t) = (term324 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140273 _26887) (@lem1140272 _26886 _26887 P t)). Qed.
Lemma lem1140275 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term318 _26886 _26887 P t) = (term324 _26886 _26887 P t).
Proof. exact (TRANS (@lem1140267 _26886 _26887 P t) (@lem1140274 _26886 _26887 P t)). Qed.
Lemma lem1140276 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term76 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140265 _26886 _26887 P x t)). Qed.
Lemma lem1140277 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140278 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term9 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140277 _26887) (@lem1140276 _26886 _26887 P t)). Qed.
Lemma lem1140279 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term325 _26886 _26887 _18849 P t) = (term325 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term325 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140280 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140282 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term326 _26886 _26887 P t) = (term327 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140281) (@lem1140275 _26886 _26887 P t)). Qed.
Lemma lem1140283 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term328 _26886 _26887 _18849 P t) = (term329 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140282 _26886 _26887 P t) (@lem1140279 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140285 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term330 _26886 _26887 P t) = (term330 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140284) (@lem1140278 _26886 _26887 P t)). Qed.
Lemma lem1140286 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term331 _26886 _26887 _18849 P t) = (term331 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140285 _26886 _26887 P t) (@lem1140280 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140288 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term332 _26886 _26887 _18849 P t) = (term332 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140287) (@lem1140286 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140289 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term333 _26886 _26887 _18849 P t) = (term334 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140288 _26886 _26887 _18849 P t) (@lem1140283 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140290 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) = (term333 _26886 _26887 _18849 P t).
Proof. exact (@lem17500 (term9 _26886 _26887 P t) (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140291 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) = (term334 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140290 _26886 _26887 _18849 P t) (@lem1140289 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140302 {A : Type'} (P : A -> Prop) (Q : Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1140303 {_26887 : Type'} (P : _26887 -> Prop) (Q : Prop) : (term335 _26887 P Q) = (term336 _26887 P Q).
Proof. exact (@lem1140302 _26887 P Q). Qed.
Lemma lem1140304 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term337 _26886 _26887 _18849 P t) = (term338 _26886 _26887 _18849 P t).
Proof. exact (@lem1140303 _26887 (term76 _26886 _26887 P t) (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140305 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1140306 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term88 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140305 _26886 _26887 P x t)). Qed.
Lemma lem1140307 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140308 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term89 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140307 _26887) (@lem1140306 _26886 _26887 P t)). Qed.
Lemma lem1140309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140310 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term339 _26886 _26887 P t) = (term330 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140309) (@lem1140308 _26886 _26887 P t)). Qed.
Lemma lem1140311 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140312 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term337 _26886 _26887 _18849 P t) = (term331 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140310 _26886 _26887 P t) (@lem1140311 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140314 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term340 _26886 _26887 _18849 P t) = (term341 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140313) (@lem1140312 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140315 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1140316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140317 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term342 _26886 _26887 P t x) = (term343 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140316) (@lem1140315 _26886 _26887 P x t)). Qed.
Lemma lem1140318 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140319 {_26886 _26887 : Type'} (x : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term344 _26886 _26887 x _18849 P t) = (term345 _26886 _26887 x _18849 P t).
Proof. exact (MK_COMB (@lem1140317 _26886 _26887 P x t) (@lem1140318 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140320 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term346 _26886 _26887 _18849 P t) = (term347 _26886 _26887 _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140319 _26886 _26887 x _18849 P t)). Qed.
Lemma lem1140321 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140322 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term338 _26886 _26887 _18849 P t) = (term348 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140321 _26887) (@lem1140320 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140323 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term337 _26886 _26887 _18849 P t) = (term338 _26886 _26887 _18849 P t)) = ((term331 _26886 _26887 _18849 P t) = (term348 _26886 _26887 _18849 P t)).
Proof. exact (MK_COMB (@lem1140314 _26886 _26887 _18849 P t) (@lem1140322 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140324 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term331 _26886 _26887 _18849 P t) = (term348 _26886 _26887 _18849 P t).
Proof. exact (EQ_MP (@lem1140323 _26886 _26887 _18849 P t) (@lem1140304 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140326 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term332 _26886 _26887 _18849 P t) = (term349 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140325) (@lem1140324 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140327 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term329 _26886 _26887 _18849 P t) = (term329 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term329 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140328 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term334 _26886 _26887 _18849 P t) = (term350 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140326 _26886 _26887 _18849 P t) (@lem1140327 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140330 {A : Type'} (P : A -> Prop) (Q : Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1140331 {_26887 : Type'} (P : _26887 -> Prop) (Q : Prop) : (term351 _26887 P Q) = (term352 _26887 P Q).
Proof. exact (@lem1140330 _26887 P Q). Qed.
Lemma lem1140332 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term353 _26886 _26887 _18849 P t) = (term354 _26886 _26887 _18849 P t).
Proof. exact (@lem1140331 _26887 (term347 _26886 _26887 _18849 P t) (term329 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140333 {_26886 _26887 : Type'} (x : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term355 _26886 _26887 _18849 P t x) = (term345 _26886 _26887 x _18849 P t).
Proof. exact (eq_refl (term355 _26886 _26887 _18849 P t x)). Qed.
Lemma lem1140334 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term356 _26886 _26887 _18849 P t) = (term347 _26886 _26887 _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140333 _26886 _26887 x _18849 P t)). Qed.
Lemma lem1140335 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140336 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term357 _26886 _26887 _18849 P t) = (term348 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140335 _26887) (@lem1140334 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140338 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term358 _26886 _26887 _18849 P t) = (term349 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140337) (@lem1140336 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140339 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term329 _26886 _26887 _18849 P t) = (term329 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term329 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140340 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term353 _26886 _26887 _18849 P t) = (term350 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140338 _26886 _26887 _18849 P t) (@lem1140339 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140342 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term359 _26886 _26887 _18849 P t) = (term360 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140341) (@lem1140340 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140343 {_26886 _26887 : Type'} (x : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term355 _26886 _26887 _18849 P t x) = (term345 _26886 _26887 x _18849 P t).
Proof. exact (eq_refl (term355 _26886 _26887 _18849 P t x)). Qed.
Lemma lem1140344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140345 {_26886 _26887 : Type'} (x : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term361 _26886 _26887 _18849 P t x) = (term362 _26886 _26887 x _18849 P t).
Proof. exact (MK_COMB (@lem1140344) (@lem1140343 _26886 _26887 x _18849 P t)). Qed.
Lemma lem1140346 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term329 _26886 _26887 _18849 P t) = (term329 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term329 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140347 {_26886 _26887 : Type'} (x : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term363 _26886 _26887 x _18849 P t) = (term364 _26886 _26887 x _18849 P t).
Proof. exact (MK_COMB (@lem1140345 _26886 _26887 x _18849 P t) (@lem1140346 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140348 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term365 _26886 _26887 _18849 P t) = (term366 _26886 _26887 _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140347 _26886 _26887 x _18849 P t)). Qed.
Lemma lem1140349 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140350 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term354 _26886 _26887 _18849 P t) = (term367 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140349 _26887) (@lem1140348 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140351 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term353 _26886 _26887 _18849 P t) = (term354 _26886 _26887 _18849 P t)) = ((term350 _26886 _26887 _18849 P t) = (term367 _26886 _26887 _18849 P t)).
Proof. exact (MK_COMB (@lem1140342 _26886 _26887 _18849 P t) (@lem1140350 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140352 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term350 _26886 _26887 _18849 P t) = (term367 _26886 _26887 _18849 P t).
Proof. exact (EQ_MP (@lem1140351 _26886 _26887 _18849 P t) (@lem1140332 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140354 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term334 _26886 _26887 _18849 P t) = (term367 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140328 _26886 _26887 _18849 P t) (@lem1140352 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140355 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) = (term367 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140291 _26886 _26887 _18849 P t) (@lem1140354 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140356 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) : term367 _26886 _26887 _18849 P t.
Proof. exact (EQ_MP (@lem1140355 _26886 _26887 _18849 P t) (@lem1139832 _26886 _26887 _18849 P t h1)). Qed.
Lemma lem1140358 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1140359 {_26887 : Type'} (P : _26887 -> Prop) : (term171 _26887 P) = (term172 _26887 P).
Proof. exact (@lem18394 _26887 P). Qed.
Lemma lem1140360 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term173 _26886 _26887 P h) = (term174 _26886 _26887 P h).
Proof. exact (@lem1140359 _26887 (term75 _26886 _26887 P h)). Qed.
Lemma lem1140361 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1140362 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140364 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term175 _26886 _26887 P h x) = (term176 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140362) (@lem1140361 _26886 _26887 P x h)). Qed.
Lemma lem1140365 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term177 _26886 _26887 P h) = (term178 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140364 _26886 _26887 P x h)). Qed.
Lemma lem1140366 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140367 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term174 _26886 _26887 P h) = (term179 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140366 _26887) (@lem1140365 _26886 _26887 P h)). Qed.
Lemma lem1140368 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term173 _26886 _26887 P h) = (term179 _26886 _26887 P h).
Proof. exact (TRANS (@lem1140360 _26886 _26887 P h) (@lem1140367 _26886 _26887 P h)). Qed.
Lemma lem1140369 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term75 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140358 _26886 _26887 P x h)). Qed.
Lemma lem1140370 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140371 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term55 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140370 _26887) (@lem1140369 _26886 _26887 P h)). Qed.
Lemma lem1140373 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term81 _26886 _26887 P x t)). Qed.
Lemma lem1140374 {_26887 : Type'} (P : _26887 -> Prop) : (term171 _26887 P) = (term172 _26887 P).
Proof. exact (@lem18394 _26887 P). Qed.
Lemma lem1140375 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term318 _26886 _26887 P t) = (term319 _26886 _26887 P t).
Proof. exact (@lem1140374 _26887 (term76 _26886 _26887 P t)). Qed.
Lemma lem1140376 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1140377 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140379 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term320 _26886 _26887 P t x) = (term321 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140377) (@lem1140376 _26886 _26887 P x t)). Qed.
Lemma lem1140380 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term322 _26886 _26887 P t) = (term323 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140379 _26886 _26887 P x t)). Qed.
Lemma lem1140381 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140382 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term319 _26886 _26887 P t) = (term324 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140381 _26887) (@lem1140380 _26886 _26887 P t)). Qed.
Lemma lem1140383 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term318 _26886 _26887 P t) = (term324 _26886 _26887 P t).
Proof. exact (TRANS (@lem1140375 _26886 _26887 P t) (@lem1140382 _26886 _26887 P t)). Qed.
Lemma lem1140384 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term76 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140373 _26886 _26887 P x t)). Qed.
Lemma lem1140385 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140386 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term9 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140385 _26887) (@lem1140384 _26886 _26887 P t)). Qed.
Lemma lem1140387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140388 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term368 _26886 _26887 P h) = (term369 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140387) (@lem1140368 _26886 _26887 P h)). Qed.
Lemma lem1140389 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term370 _26886 _26887 h P t) = (term371 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140388 _26886 _26887 P h) (@lem1140383 _26886 _26887 P t)). Qed.
Lemma lem1140390 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term372 _26886 _26887 h P t) = (term370 _26886 _26887 h P t).
Proof. exact (@lem17160 (term55 _26886 _26887 P h) (term9 _26886 _26887 P t)). Qed.
Lemma lem1140391 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term372 _26886 _26887 h P t) = (term371 _26886 _26887 h P t).
Proof. exact (TRANS (@lem1140390 _26886 _26887 h P t) (@lem1140389 _26886 _26887 h P t)). Qed.
Lemma lem1140392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140393 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term60 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140392) (@lem1140371 _26886 _26887 P h)). Qed.
Lemma lem1140394 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term90 _26886 _26887 h P t) = (term90 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140393 _26886 _26887 P h) (@lem1140386 _26886 _26887 P t)). Qed.
Lemma lem1140396 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1140397 {_26887 : Type'} (P : _26887 -> Prop) : (term171 _26887 P) = (term172 _26887 P).
Proof. exact (@lem18394 _26887 P). Qed.
Lemma lem1140398 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term173 _26886 _26887 P h) = (term174 _26886 _26887 P h).
Proof. exact (@lem1140397 _26887 (term75 _26886 _26887 P h)). Qed.
Lemma lem1140399 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1140400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140402 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term175 _26886 _26887 P h x) = (term176 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140400) (@lem1140399 _26886 _26887 P x h)). Qed.
Lemma lem1140403 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term177 _26886 _26887 P h) = (term178 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140402 _26886 _26887 P x h)). Qed.
Lemma lem1140404 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140405 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term174 _26886 _26887 P h) = (term179 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140404 _26887) (@lem1140403 _26886 _26887 P h)). Qed.
Lemma lem1140406 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term173 _26886 _26887 P h) = (term179 _26886 _26887 P h).
Proof. exact (TRANS (@lem1140398 _26886 _26887 P h) (@lem1140405 _26886 _26887 P h)). Qed.
Lemma lem1140407 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term75 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140396 _26886 _26887 P x h)). Qed.
Lemma lem1140408 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140409 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term55 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140408 _26887) (@lem1140407 _26886 _26887 P h)). Qed.
Lemma lem1140410 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term325 _26886 _26887 _18849 P t) = (term325 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term325 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140411 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140413 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term368 _26886 _26887 P h) = (term369 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140412) (@lem1140406 _26886 _26887 P h)). Qed.
Lemma lem1140414 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term373 _26886 _26887 h _18849 P t) = (term374 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140413 _26886 _26887 P h) (@lem1140410 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140415 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term375 _26886 _26887 h _18849 P t) = (term373 _26886 _26887 h _18849 P t).
Proof. exact (@lem17160 (term55 _26886 _26887 P h) (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140416 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term375 _26886 _26887 h _18849 P t) = (term374 _26886 _26887 h _18849 P t).
Proof. exact (TRANS (@lem1140415 _26886 _26887 h _18849 P t) (@lem1140414 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140418 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term60 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140417) (@lem1140409 _26886 _26887 P h)). Qed.
Lemma lem1140419 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term111 _26886 _26887 h _18849 P t) = (term111 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140418 _26886 _26887 P h) (@lem1140411 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140421 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term376 _26886 _26887 h P t) = (term377 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140420) (@lem1140391 _26886 _26887 h P t)). Qed.
Lemma lem1140422 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term378 _26886 _26887 h _18849 P t) = (term379 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140421 _26886 _26887 h P t) (@lem1140419 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140424 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term380 _26886 _26887 h P t) = (term380 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140423) (@lem1140394 _26886 _26887 h P t)). Qed.
Lemma lem1140425 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term381 _26886 _26887 h _18849 P t) = (term382 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140424 _26886 _26887 h P t) (@lem1140416 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140427 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term383 _26886 _26887 h _18849 P t) = (term384 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140426) (@lem1140425 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140428 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term385 _26886 _26887 h _18849 P t) = (term386 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140427 _26886 _26887 h _18849 P t) (@lem1140422 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140429 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term170 _26886 _26887 h _18849 P t) = (term385 _26886 _26887 h _18849 P t).
Proof. exact (@lem17646 (term90 _26886 _26887 h P t) (term111 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140430 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term170 _26886 _26887 h _18849 P t) = (term386 _26886 _26887 h _18849 P t).
Proof. exact (TRANS (@lem1140429 _26886 _26887 h _18849 P t) (@lem1140428 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term72 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1140458 {_26887 : Type'} (P : _26887 -> Prop) (Q : _26887 -> Prop) : (term72 _26887 P Q) = (term71 _26887 P Q).
Proof. exact (@lem1140457 _26887 P Q). Qed.
Lemma lem1140459 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term74 _26886 _26887 h P t) = (term73 _26886 _26887 h P t).
Proof. exact (@lem1140458 _26887 (term75 _26886 _26887 P h) (term76 _26886 _26887 P t)). Qed.
Lemma lem1140460 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1140461 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term85 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140460 _26886 _26887 P x h)). Qed.
Lemma lem1140462 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140463 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term86 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140462 _26887) (@lem1140461 _26886 _26887 P h)). Qed.
Lemma lem1140464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140465 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term87 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140464) (@lem1140463 _26886 _26887 P h)). Qed.
Lemma lem1140466 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1140467 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term88 _26886 _26887 P t) = (term76 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140466 _26886 _26887 P x t)). Qed.
Lemma lem1140468 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140469 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term89 _26886 _26887 P t) = (term9 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140468 _26887) (@lem1140467 _26886 _26887 P t)). Qed.
Lemma lem1140470 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term74 _26886 _26887 h P t) = (term90 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140465 _26886 _26887 P h) (@lem1140469 _26886 _26887 P t)). Qed.
Lemma lem1140471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140472 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term387 _26886 _26887 h P t) = (term91 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140471) (@lem1140470 _26886 _26887 h P t)). Qed.
Lemma lem1140473 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1140474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140475 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term78 _26886 _26887 P h x) = (term79 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140474) (@lem1140473 _26886 _26887 P x h)). Qed.
Lemma lem1140476 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term80 _26886 _26887 P t x) = (term81 _26886 _26887 P x t).
Proof. exact (eq_refl (term80 _26886 _26887 P t x)). Qed.
Lemma lem1140477 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term82 _26886 _26887 h P t x) = (term44 _26886 _26887 h P x t).
Proof. exact (MK_COMB (@lem1140475 _26886 _26887 P x h) (@lem1140476 _26886 _26887 P x t)). Qed.
Lemma lem1140478 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term83 _26886 _26887 h P t) = (term46 _26886 _26887 h P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140477 _26886 _26887 h P x t)). Qed.
Lemma lem1140479 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140480 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term73 _26886 _26887 h P t) = (term47 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140479 _26887) (@lem1140478 _26886 _26887 h P t)). Qed.
Lemma lem1140481 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : ((term74 _26886 _26887 h P t) = (term73 _26886 _26887 h P t)) = ((term90 _26886 _26887 h P t) = (term47 _26886 _26887 h P t)).
Proof. exact (MK_COMB (@lem1140472 _26886 _26887 h P t) (@lem1140480 _26886 _26887 h P t)). Qed.
Lemma lem1140482 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term90 _26886 _26887 h P t) = (term47 _26886 _26887 h P t).
Proof. exact (EQ_MP (@lem1140481 _26886 _26887 h P t) (@lem1140459 _26886 _26887 h P t)). Qed.
Lemma lem1140483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140484 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term380 _26886 _26887 h P t) = (term388 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140483) (@lem1140482 _26886 _26887 h P t)). Qed.
Lemma lem1140485 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term374 _26886 _26887 h _18849 P t) = (term374 _26886 _26887 h _18849 P t).
Proof. exact (eq_refl (term374 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140486 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term382 _26886 _26887 h _18849 P t) = (term389 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140484 _26886 _26887 h P t) (@lem1140485 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140488 {A : Type'} (P : A -> Prop) (Q : Prop) : (term335 A P Q) = (term336 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1140489 {_26887 : Type'} (P : _26887 -> Prop) (Q : Prop) : (term335 _26887 P Q) = (term336 _26887 P Q).
Proof. exact (@lem1140488 _26887 P Q). Qed.
Lemma lem1140490 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term390 _26886 _26887 h _18849 P t) = (term391 _26886 _26887 h _18849 P t).
Proof. exact (@lem1140489 _26887 (term46 _26886 _26887 h P t) (term374 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140491 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term392 _26886 _26887 h P t x) = (term44 _26886 _26887 h P x t).
Proof. exact (eq_refl (term392 _26886 _26887 h P t x)). Qed.
Lemma lem1140492 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term393 _26886 _26887 h P t) = (term46 _26886 _26887 h P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140491 _26886 _26887 h P x t)). Qed.
Lemma lem1140493 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140494 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term394 _26886 _26887 h P t) = (term47 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140493 _26887) (@lem1140492 _26886 _26887 h P t)). Qed.
Lemma lem1140495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140496 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term395 _26886 _26887 h P t) = (term388 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140495) (@lem1140494 _26886 _26887 h P t)). Qed.
Lemma lem1140497 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term374 _26886 _26887 h _18849 P t) = (term374 _26886 _26887 h _18849 P t).
Proof. exact (eq_refl (term374 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140498 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term390 _26886 _26887 h _18849 P t) = (term389 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140496 _26886 _26887 h P t) (@lem1140497 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140500 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term396 _26886 _26887 h _18849 P t) = (term397 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140499) (@lem1140498 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140501 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term392 _26886 _26887 h P t x) = (term44 _26886 _26887 h P x t).
Proof. exact (eq_refl (term392 _26886 _26887 h P t x)). Qed.
Lemma lem1140502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140503 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term398 _26886 _26887 h P t x) = (term399 _26886 _26887 h P x t).
Proof. exact (MK_COMB (@lem1140502) (@lem1140501 _26886 _26887 h P x t)). Qed.
Lemma lem1140504 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term374 _26886 _26887 h _18849 P t) = (term374 _26886 _26887 h _18849 P t).
Proof. exact (eq_refl (term374 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140505 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term400 _26886 _26887 x h _18849 P t) = (term401 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140503 _26886 _26887 h P x t) (@lem1140504 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140506 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term402 _26886 _26887 h _18849 P t) = (term403 _26886 _26887 h _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140505 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140507 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140508 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term391 _26886 _26887 h _18849 P t) = (term404 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140507 _26887) (@lem1140506 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140509 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term390 _26886 _26887 h _18849 P t) = (term391 _26886 _26887 h _18849 P t)) = ((term389 _26886 _26887 h _18849 P t) = (term404 _26886 _26887 h _18849 P t)).
Proof. exact (MK_COMB (@lem1140500 _26886 _26887 h _18849 P t) (@lem1140508 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140510 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term389 _26886 _26887 h _18849 P t) = (term404 _26886 _26887 h _18849 P t).
Proof. exact (EQ_MP (@lem1140509 _26886 _26887 h _18849 P t) (@lem1140490 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140511 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term382 _26886 _26887 h _18849 P t) = (term404 _26886 _26887 h _18849 P t).
Proof. exact (TRANS (@lem1140486 _26886 _26887 h _18849 P t) (@lem1140510 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140513 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term384 _26886 _26887 h _18849 P t) = (term405 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140512) (@lem1140511 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140515 {A : Type'} (P : A -> Prop) (Q : Prop) : (term351 A P Q) = (term352 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1140516 {_26887 : Type'} (P : _26887 -> Prop) (Q : Prop) : (term351 _26887 P Q) = (term352 _26887 P Q).
Proof. exact (@lem1140515 _26887 P Q). Qed.
Lemma lem1140517 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term406 _26886 _26887 h _18849 P t) = (term407 _26886 _26887 h _18849 P t).
Proof. exact (@lem1140516 _26887 (term75 _26886 _26887 P h) (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140518 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1140519 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term85 _26886 _26887 P h) = (term75 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140518 _26886 _26887 P x h)). Qed.
Lemma lem1140520 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140521 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term86 _26886 _26887 P h) = (term55 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140520 _26887) (@lem1140519 _26886 _26887 P h)). Qed.
Lemma lem1140522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140523 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term87 _26886 _26887 P h) = (term60 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140522) (@lem1140521 _26886 _26887 P h)). Qed.
Lemma lem1140524 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140525 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term406 _26886 _26887 h _18849 P t) = (term111 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140523 _26886 _26887 P h) (@lem1140524 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140527 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term408 _26886 _26887 h _18849 P t) = (term409 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140526) (@lem1140525 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140528 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term77 _26886 _26887 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26886 _26887 P h x)). Qed.
Lemma lem1140529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140530 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term78 _26886 _26887 P h x) = (term79 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140529) (@lem1140528 _26886 _26887 P x h)). Qed.
Lemma lem1140531 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term110 _26886 _26887 _18849 P t).
Proof. exact (eq_refl (term110 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140532 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term410 _26886 _26887 h x _18849 P t) = (term411 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140530 _26886 _26887 P x h) (@lem1140531 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140533 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term412 _26886 _26887 h _18849 P t) = (term413 _26886 _26887 h _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140532 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140534 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140535 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term407 _26886 _26887 h _18849 P t) = (term414 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140534 _26887) (@lem1140533 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140536 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term406 _26886 _26887 h _18849 P t) = (term407 _26886 _26887 h _18849 P t)) = ((term111 _26886 _26887 h _18849 P t) = (term414 _26886 _26887 h _18849 P t)).
Proof. exact (MK_COMB (@lem1140527 _26886 _26887 h _18849 P t) (@lem1140535 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140537 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term111 _26886 _26887 h _18849 P t) = (term414 _26886 _26887 h _18849 P t).
Proof. exact (EQ_MP (@lem1140536 _26886 _26887 h _18849 P t) (@lem1140517 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140538 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term377 _26886 _26887 h P t) = (term377 _26886 _26887 h P t).
Proof. exact (eq_refl (term377 _26886 _26887 h P t)). Qed.
Lemma lem1140539 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term379 _26886 _26887 h _18849 P t) = (term415 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140538 _26886 _26887 h P t) (@lem1140537 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140541 {A : Type'} (P : Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1140542 {_26887 : Type'} (P : Prop) (Q : _26887 -> Prop) : (term302 _26887 P Q) = (term303 _26887 P Q).
Proof. exact (@lem1140541 _26887 P Q). Qed.
Lemma lem1140543 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term416 _26886 _26887 h _18849 P t) = (term417 _26886 _26887 h _18849 P t).
Proof. exact (@lem1140542 _26887 (term371 _26886 _26887 h P t) (term413 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140544 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term418 _26886 _26887 h _18849 P t x) = (term411 _26886 _26887 x h _18849 P t).
Proof. exact (eq_refl (term418 _26886 _26887 h _18849 P t x)). Qed.
Lemma lem1140545 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term419 _26886 _26887 h _18849 P t) = (term413 _26886 _26887 h _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140544 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140546 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140547 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term420 _26886 _26887 h _18849 P t) = (term414 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140546 _26887) (@lem1140545 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140548 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term377 _26886 _26887 h P t) = (term377 _26886 _26887 h P t).
Proof. exact (eq_refl (term377 _26886 _26887 h P t)). Qed.
Lemma lem1140549 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term416 _26886 _26887 h _18849 P t) = (term415 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140548 _26886 _26887 h P t) (@lem1140547 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140551 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term421 _26886 _26887 h _18849 P t) = (term422 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140550) (@lem1140549 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140552 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term418 _26886 _26887 h _18849 P t x) = (term411 _26886 _26887 x h _18849 P t).
Proof. exact (eq_refl (term418 _26886 _26887 h _18849 P t x)). Qed.
Lemma lem1140553 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term377 _26886 _26887 h P t) = (term377 _26886 _26887 h P t).
Proof. exact (eq_refl (term377 _26886 _26887 h P t)). Qed.
Lemma lem1140554 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term423 _26886 _26887 h _18849 P t x) = (term424 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140553 _26886 _26887 h P t) (@lem1140552 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140555 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term425 _26886 _26887 h _18849 P t) = (term426 _26886 _26887 h _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140554 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140556 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140557 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term417 _26886 _26887 h _18849 P t) = (term427 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140556 _26887) (@lem1140555 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140558 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term416 _26886 _26887 h _18849 P t) = (term417 _26886 _26887 h _18849 P t)) = ((term415 _26886 _26887 h _18849 P t) = (term427 _26886 _26887 h _18849 P t)).
Proof. exact (MK_COMB (@lem1140551 _26886 _26887 h _18849 P t) (@lem1140557 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140559 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term415 _26886 _26887 h _18849 P t) = (term427 _26886 _26887 h _18849 P t).
Proof. exact (EQ_MP (@lem1140558 _26886 _26887 h _18849 P t) (@lem1140543 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140560 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term379 _26886 _26887 h _18849 P t) = (term427 _26886 _26887 h _18849 P t).
Proof. exact (TRANS (@lem1140539 _26886 _26887 h _18849 P t) (@lem1140559 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140561 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term386 _26886 _26887 h _18849 P t) = (term428 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140513 _26886 _26887 h _18849 P t) (@lem1140560 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140563 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term72 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1140564 {_26887 : Type'} (P : _26887 -> Prop) (Q : _26887 -> Prop) : (term72 _26887 P Q) = (term71 _26887 P Q).
Proof. exact (@lem1140563 _26887 P Q). Qed.
Lemma lem1140565 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term429 _26886 _26887 h _18849 P t) = (term430 _26886 _26887 h _18849 P t).
Proof. exact (@lem1140564 _26887 (term403 _26886 _26887 h _18849 P t) (term426 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140566 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term431 _26886 _26887 h _18849 P t x) = (term401 _26886 _26887 x h _18849 P t).
Proof. exact (eq_refl (term431 _26886 _26887 h _18849 P t x)). Qed.
Lemma lem1140567 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term432 _26886 _26887 h _18849 P t) = (term403 _26886 _26887 h _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140566 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140568 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140569 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term433 _26886 _26887 h _18849 P t) = (term404 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140568 _26887) (@lem1140567 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140571 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term434 _26886 _26887 h _18849 P t) = (term405 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140570) (@lem1140569 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140572 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term435 _26886 _26887 h _18849 P t x) = (term424 _26886 _26887 x h _18849 P t).
Proof. exact (eq_refl (term435 _26886 _26887 h _18849 P t x)). Qed.
Lemma lem1140573 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term436 _26886 _26887 h _18849 P t) = (term426 _26886 _26887 h _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140572 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140574 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140575 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term437 _26886 _26887 h _18849 P t) = (term427 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140574 _26887) (@lem1140573 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140576 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term429 _26886 _26887 h _18849 P t) = (term428 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140571 _26886 _26887 h _18849 P t) (@lem1140575 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1140578 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term438 _26886 _26887 h _18849 P t) = (term439 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140577) (@lem1140576 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140579 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term431 _26886 _26887 h _18849 P t x) = (term401 _26886 _26887 x h _18849 P t).
Proof. exact (eq_refl (term431 _26886 _26887 h _18849 P t x)). Qed.
Lemma lem1140580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140581 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term440 _26886 _26887 h _18849 P t x) = (term441 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140580) (@lem1140579 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140582 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term435 _26886 _26887 h _18849 P t x) = (term424 _26886 _26887 x h _18849 P t).
Proof. exact (eq_refl (term435 _26886 _26887 h _18849 P t x)). Qed.
Lemma lem1140583 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term442 _26886 _26887 h _18849 P t x) = (term443 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140581 _26886 _26887 x h _18849 P t) (@lem1140582 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140584 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term444 _26886 _26887 h _18849 P t) = (term445 _26886 _26887 h _18849 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140583 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140585 {_26887 : Type'} : (@ex _26887) = (@ex _26887).
Proof. exact (eq_refl (@ex _26887)). Qed.
Lemma lem1140586 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term430 _26886 _26887 h _18849 P t) = (term446 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140585 _26887) (@lem1140584 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140587 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : ((term429 _26886 _26887 h _18849 P t) = (term430 _26886 _26887 h _18849 P t)) = ((term428 _26886 _26887 h _18849 P t) = (term446 _26886 _26887 h _18849 P t)).
Proof. exact (MK_COMB (@lem1140578 _26886 _26887 h _18849 P t) (@lem1140586 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140588 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term428 _26886 _26887 h _18849 P t) = (term446 _26886 _26887 h _18849 P t).
Proof. exact (EQ_MP (@lem1140587 _26886 _26887 h _18849 P t) (@lem1140565 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140590 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term386 _26886 _26887 h _18849 P t) = (term446 _26886 _26887 h _18849 P t).
Proof. exact (TRANS (@lem1140561 _26886 _26887 h _18849 P t) (@lem1140588 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140591 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term170 _26886 _26887 h _18849 P t) = (term446 _26886 _26887 h _18849 P t).
Proof. exact (TRANS (@lem1140430 _26886 _26887 h _18849 P t) (@lem1140590 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140592 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term170 _26886 _26887 h _18849 P t) : term446 _26886 _26887 h _18849 P t.
Proof. exact (EQ_MP (@lem1140591 _26886 _26887 h _18849 P t) (@lem1139837 _26886 _26887 h _18849 P t h1)). Qed.
Lemma lem1140593 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term443 _26886 _26887 x h _18849 P t) : term443 _26886 _26887 x h _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1140594 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term364 _26886 _26887 x' _18849 P t) : term364 _26886 _26887 x' _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1140596 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140601 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140602 {_26886 _26887 : Type'} (f : type740 _26886 _26887) (x : type1470 _26886 _26887) : (f x) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) f x).
Proof. exact (@lem1140601 (type1470 _26886 _26887) (_26886 -> Prop) f x). Qed.
Lemma lem1140604 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (_18849 P) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P).
Proof. exact (@lem1140602 _26886 _26887 _18849 P). Qed.
Lemma lem1140605 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140606 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term109 _26886 _26887 _18849 P) = (term447 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140596 _26886) (@lem1140604 _26886 _26887 _18849 P)). Qed.
Lemma lem1140607 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term448 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140606 _26886 _26887 _18849 P) (@lem1140605 _26886 t)). Qed.
Lemma lem1140609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140610 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140609 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140611 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term447 _26886 _26887 _18849 P) = (term449 _26886 _26887 _18849 P).
Proof. exact (@lem1140610 _26886 (@EX _26886) (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P)). Qed.
Lemma lem1140612 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140613 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term450 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140611 _26886 _26887 _18849 P) (@lem1140612 _26886 t)). Qed.
Lemma lem1140615 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140616 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140615 (list _26886) Prop f x). Qed.
Lemma lem1140617 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term450 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (@lem1140616 _26886 (term449 _26886 _26887 _18849 P) t). Qed.
Lemma lem1140618 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140613 _26886 _26887 _18849 P t) (@lem1140617 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140619 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140607 _26886 _26887 _18849 P t) (@lem1140618 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140627 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140626 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140628 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (P x) = (@I (_26887 -> _26886 -> Prop) P x).
Proof. exact (@lem1140627 _26886 _26887 P x). Qed.
Lemma lem1140629 {_26886 : Type'} (h : _26886) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1140630 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (@I (_26887 -> _26886 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1140628 _26886 _26887 P x) (@lem1140629 _26886 h)). Qed.
Lemma lem1140632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140633 {_26886 : Type'} (f : _26886 -> Prop) (x : _26886) : (f x) = (@I (_26886 -> Prop) f x).
Proof. exact (@lem1140632 _26886 Prop f x). Qed.
Lemma lem1140634 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (@I (_26887 -> _26886 -> Prop) P x h) = (term452 _26886 _26887 P x h).
Proof. exact (@lem1140633 _26886 (@I (_26887 -> _26886 -> Prop) P x) h). Qed.
Lemma lem1140636 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (term452 _26886 _26887 P x h).
Proof. exact (TRANS (@lem1140630 _26886 _26887 P x h) (@lem1140634 _26886 _26887 P x h)). Qed.
Lemma lem1140637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140638 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term79 _26886 _26887 P x h) = (term453 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140637) (@lem1140636 _26886 _26887 P x h)). Qed.
Lemma lem1140639 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term411 _26886 _26887 x h _18849 P t) = (term454 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140638 _26886 _26887 P x h) (@lem1140619 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140640 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140641 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140646 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140647 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140646 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140649 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (P x) = (@I (_26887 -> _26886 -> Prop) P x).
Proof. exact (@lem1140647 _26886 _26887 P x). Qed.
Lemma lem1140650 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140651 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (term455 _26886 _26887 P x) = (term456 _26886 _26887 P x).
Proof. exact (MK_COMB (@lem1140641 _26886) (@lem1140649 _26886 _26887 P x)). Qed.
Lemma lem1140652 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term457 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140651 _26886 _26887 P x) (@lem1140650 _26886 t)). Qed.
Lemma lem1140654 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140655 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140654 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140656 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (term456 _26886 _26887 P x) = (term458 _26886 _26887 P x).
Proof. exact (@lem1140655 _26886 (@EX _26886) (@I (_26887 -> _26886 -> Prop) P x)). Qed.
Lemma lem1140657 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140658 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term457 _26886 _26887 P x t) = (term459 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140656 _26886 _26887 P x) (@lem1140657 _26886 t)). Qed.
Lemma lem1140660 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140661 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140660 (list _26886) Prop f x). Qed.
Lemma lem1140662 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term459 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (@lem1140661 _26886 (term458 _26886 _26887 P x) t). Qed.
Lemma lem1140663 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term457 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (TRANS (@lem1140658 _26886 _26887 P x t) (@lem1140662 _26886 _26887 P x t)). Qed.
Lemma lem1140664 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (TRANS (@lem1140652 _26886 _26887 P x t) (@lem1140663 _26886 _26887 P x t)). Qed.
Lemma lem1140665 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term321 _26886 _26887 P x t) = (term461 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140640) (@lem1140664 _26886 _26887 P x t)). Qed.
Lemma lem1140666 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term323 _26886 _26887 P t) = (term462 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140665 _26886 _26887 P x t)). Qed.
Lemma lem1140667 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140668 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term324 _26886 _26887 P t) = (term463 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140667 _26887) (@lem1140666 _26886 _26887 P t)). Qed.
Lemma lem1140669 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140676 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140677 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140676 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140678 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (P x) = (@I (_26887 -> _26886 -> Prop) P x).
Proof. exact (@lem1140677 _26886 _26887 P x). Qed.
Lemma lem1140679 {_26886 : Type'} (h : _26886) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1140680 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (@I (_26887 -> _26886 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1140678 _26886 _26887 P x) (@lem1140679 _26886 h)). Qed.
Lemma lem1140682 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140683 {_26886 : Type'} (f : _26886 -> Prop) (x : _26886) : (f x) = (@I (_26886 -> Prop) f x).
Proof. exact (@lem1140682 _26886 Prop f x). Qed.
Lemma lem1140684 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (@I (_26887 -> _26886 -> Prop) P x h) = (term452 _26886 _26887 P x h).
Proof. exact (@lem1140683 _26886 (@I (_26887 -> _26886 -> Prop) P x) h). Qed.
Lemma lem1140686 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (term452 _26886 _26887 P x h).
Proof. exact (TRANS (@lem1140680 _26886 _26887 P x h) (@lem1140684 _26886 _26887 P x h)). Qed.
Lemma lem1140687 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term176 _26886 _26887 P x h) = (term464 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140669) (@lem1140686 _26886 _26887 P x h)). Qed.
Lemma lem1140688 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term178 _26886 _26887 P h) = (term465 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140687 _26886 _26887 P x h)). Qed.
Lemma lem1140689 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140690 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term179 _26886 _26887 P h) = (term466 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140689 _26887) (@lem1140688 _26886 _26887 P h)). Qed.
Lemma lem1140691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140692 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term369 _26886 _26887 P h) = (term467 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140691) (@lem1140690 _26886 _26887 P h)). Qed.
Lemma lem1140693 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term371 _26886 _26887 h P t) = (term468 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140692 _26886 _26887 P h) (@lem1140668 _26886 _26887 P t)). Qed.
Lemma lem1140694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140695 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term377 _26886 _26887 h P t) = (term469 _26886 _26887 h P t).
Proof. exact (MK_COMB (@lem1140694) (@lem1140693 _26886 _26887 h P t)). Qed.
Lemma lem1140696 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term424 _26886 _26887 x h _18849 P t) = (term470 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140695 _26886 _26887 h P t) (@lem1140639 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140698 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140703 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140704 {_26886 _26887 : Type'} (f : type740 _26886 _26887) (x : type1470 _26886 _26887) : (f x) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) f x).
Proof. exact (@lem1140703 (type1470 _26886 _26887) (_26886 -> Prop) f x). Qed.
Lemma lem1140706 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (_18849 P) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P).
Proof. exact (@lem1140704 _26886 _26887 _18849 P). Qed.
Lemma lem1140707 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140708 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term109 _26886 _26887 _18849 P) = (term447 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140698 _26886) (@lem1140706 _26886 _26887 _18849 P)). Qed.
Lemma lem1140709 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term448 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140708 _26886 _26887 _18849 P) (@lem1140707 _26886 t)). Qed.
Lemma lem1140711 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140712 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140711 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140713 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term447 _26886 _26887 _18849 P) = (term449 _26886 _26887 _18849 P).
Proof. exact (@lem1140712 _26886 (@EX _26886) (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P)). Qed.
Lemma lem1140714 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140715 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term450 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140713 _26886 _26887 _18849 P) (@lem1140714 _26886 t)). Qed.
Lemma lem1140717 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140718 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140717 (list _26886) Prop f x). Qed.
Lemma lem1140719 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term450 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (@lem1140718 _26886 (term449 _26886 _26887 _18849 P) t). Qed.
Lemma lem1140720 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140715 _26886 _26887 _18849 P t) (@lem1140719 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140721 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140709 _26886 _26887 _18849 P t) (@lem1140720 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140722 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term325 _26886 _26887 _18849 P t) = (term471 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140697) (@lem1140721 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140730 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140731 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140730 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140732 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (P x) = (@I (_26887 -> _26886 -> Prop) P x).
Proof. exact (@lem1140731 _26886 _26887 P x). Qed.
Lemma lem1140733 {_26886 : Type'} (h : _26886) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1140734 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (@I (_26887 -> _26886 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1140732 _26886 _26887 P x) (@lem1140733 _26886 h)). Qed.
Lemma lem1140736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140737 {_26886 : Type'} (f : _26886 -> Prop) (x : _26886) : (f x) = (@I (_26886 -> Prop) f x).
Proof. exact (@lem1140736 _26886 Prop f x). Qed.
Lemma lem1140738 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (@I (_26887 -> _26886 -> Prop) P x h) = (term452 _26886 _26887 P x h).
Proof. exact (@lem1140737 _26886 (@I (_26887 -> _26886 -> Prop) P x) h). Qed.
Lemma lem1140740 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (term452 _26886 _26887 P x h).
Proof. exact (TRANS (@lem1140734 _26886 _26887 P x h) (@lem1140738 _26886 _26887 P x h)). Qed.
Lemma lem1140741 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term176 _26886 _26887 P x h) = (term464 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140723) (@lem1140740 _26886 _26887 P x h)). Qed.
Lemma lem1140742 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term178 _26886 _26887 P h) = (term465 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1140741 _26886 _26887 P x h)). Qed.
Lemma lem1140743 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140744 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term179 _26886 _26887 P h) = (term466 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140743 _26887) (@lem1140742 _26886 _26887 P h)). Qed.
Lemma lem1140745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140746 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term369 _26886 _26887 P h) = (term467 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1140745) (@lem1140744 _26886 _26887 P h)). Qed.
Lemma lem1140747 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term374 _26886 _26887 h _18849 P t) = (term472 _26886 _26887 h _18849 P t).
Proof. exact (MK_COMB (@lem1140746 _26886 _26887 P h) (@lem1140722 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140748 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140753 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140754 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140753 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140756 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (P x) = (@I (_26887 -> _26886 -> Prop) P x).
Proof. exact (@lem1140754 _26886 _26887 P x). Qed.
Lemma lem1140757 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140758 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (term455 _26886 _26887 P x) = (term456 _26886 _26887 P x).
Proof. exact (MK_COMB (@lem1140748 _26886) (@lem1140756 _26886 _26887 P x)). Qed.
Lemma lem1140759 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term457 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140758 _26886 _26887 P x) (@lem1140757 _26886 t)). Qed.
Lemma lem1140761 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140762 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140761 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140763 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (term456 _26886 _26887 P x) = (term458 _26886 _26887 P x).
Proof. exact (@lem1140762 _26886 (@EX _26886) (@I (_26887 -> _26886 -> Prop) P x)). Qed.
Lemma lem1140764 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140765 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term457 _26886 _26887 P x t) = (term459 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140763 _26886 _26887 P x) (@lem1140764 _26886 t)). Qed.
Lemma lem1140767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140768 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140767 (list _26886) Prop f x). Qed.
Lemma lem1140769 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term459 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (@lem1140768 _26886 (term458 _26886 _26887 P x) t). Qed.
Lemma lem1140770 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term457 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (TRANS (@lem1140765 _26886 _26887 P x t) (@lem1140769 _26886 _26887 P x t)). Qed.
Lemma lem1140771 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (TRANS (@lem1140759 _26886 _26887 P x t) (@lem1140770 _26886 _26887 P x t)). Qed.
Lemma lem1140778 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140779 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140778 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140780 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (P x) = (@I (_26887 -> _26886 -> Prop) P x).
Proof. exact (@lem1140779 _26886 _26887 P x). Qed.
Lemma lem1140781 {_26886 : Type'} (h : _26886) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1140782 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (@I (_26887 -> _26886 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1140780 _26886 _26887 P x) (@lem1140781 _26886 h)). Qed.
Lemma lem1140784 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140785 {_26886 : Type'} (f : _26886 -> Prop) (x : _26886) : (f x) = (@I (_26886 -> Prop) f x).
Proof. exact (@lem1140784 _26886 Prop f x). Qed.
Lemma lem1140786 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (@I (_26887 -> _26886 -> Prop) P x h) = (term452 _26886 _26887 P x h).
Proof. exact (@lem1140785 _26886 (@I (_26887 -> _26886 -> Prop) P x) h). Qed.
Lemma lem1140788 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (P x h) = (term452 _26886 _26887 P x h).
Proof. exact (TRANS (@lem1140782 _26886 _26887 P x h) (@lem1140786 _26886 _26887 P x h)). Qed.
Lemma lem1140789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140790 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term79 _26886 _26887 P x h) = (term453 _26886 _26887 P x h).
Proof. exact (MK_COMB (@lem1140789) (@lem1140788 _26886 _26887 P x h)). Qed.
Lemma lem1140791 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term44 _26886 _26887 h P x t) = (term473 _26886 _26887 h P x t).
Proof. exact (MK_COMB (@lem1140790 _26886 _26887 P x h) (@lem1140771 _26886 _26887 P x t)). Qed.
Lemma lem1140792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140793 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term399 _26886 _26887 h P x t) = (term474 _26886 _26887 h P x t).
Proof. exact (MK_COMB (@lem1140792) (@lem1140791 _26886 _26887 h P x t)). Qed.
Lemma lem1140794 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term401 _26886 _26887 x h _18849 P t) = (term475 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140793 _26886 _26887 h P x t) (@lem1140747 _26886 _26887 h _18849 P t)). Qed.
Lemma lem1140795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140796 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term441 _26886 _26887 x h _18849 P t) = (term476 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140795) (@lem1140794 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140797 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term443 _26886 _26887 x h _18849 P t) = (term477 _26886 _26887 x h _18849 P t).
Proof. exact (MK_COMB (@lem1140796 _26886 _26887 x h _18849 P t) (@lem1140696 _26886 _26887 x h _18849 P t)). Qed.
Lemma lem1140798 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term443 _26886 _26887 x h _18849 P t) : term477 _26886 _26887 x h _18849 P t.
Proof. exact (EQ_MP (@lem1140797 _26886 _26887 x h _18849 P t) (@lem1140593 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1140799 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140800 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140805 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140806 {_26886 _26887 : Type'} (f : type740 _26886 _26887) (x : type1470 _26886 _26887) : (f x) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) f x).
Proof. exact (@lem1140805 (type1470 _26886 _26887) (_26886 -> Prop) f x). Qed.
Lemma lem1140808 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (_18849 P) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P).
Proof. exact (@lem1140806 _26886 _26887 _18849 P). Qed.
Lemma lem1140809 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140810 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term109 _26886 _26887 _18849 P) = (term447 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140800 _26886) (@lem1140808 _26886 _26887 _18849 P)). Qed.
Lemma lem1140811 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term448 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140810 _26886 _26887 _18849 P) (@lem1140809 _26886 t)). Qed.
Lemma lem1140813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140814 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140813 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140815 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term447 _26886 _26887 _18849 P) = (term449 _26886 _26887 _18849 P).
Proof. exact (@lem1140814 _26886 (@EX _26886) (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P)). Qed.
Lemma lem1140816 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140817 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term450 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140815 _26886 _26887 _18849 P) (@lem1140816 _26886 t)). Qed.
Lemma lem1140819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140820 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140819 (list _26886) Prop f x). Qed.
Lemma lem1140821 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term450 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (@lem1140820 _26886 (term449 _26886 _26887 _18849 P) t). Qed.
Lemma lem1140822 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140817 _26886 _26887 _18849 P t) (@lem1140821 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140823 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140811 _26886 _26887 _18849 P t) (@lem1140822 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140824 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term325 _26886 _26887 _18849 P t) = (term471 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140799) (@lem1140823 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1140826 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140831 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140832 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140831 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140834 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (P x) = (@I (_26887 -> _26886 -> Prop) P x).
Proof. exact (@lem1140832 _26886 _26887 P x). Qed.
Lemma lem1140835 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140836 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (term455 _26886 _26887 P x) = (term456 _26886 _26887 P x).
Proof. exact (MK_COMB (@lem1140826 _26886) (@lem1140834 _26886 _26887 P x)). Qed.
Lemma lem1140837 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term457 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140836 _26886 _26887 P x) (@lem1140835 _26886 t)). Qed.
Lemma lem1140839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140840 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140839 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140841 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) : (term456 _26886 _26887 P x) = (term458 _26886 _26887 P x).
Proof. exact (@lem1140840 _26886 (@EX _26886) (@I (_26887 -> _26886 -> Prop) P x)). Qed.
Lemma lem1140842 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140843 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term457 _26886 _26887 P x t) = (term459 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140841 _26886 _26887 P x) (@lem1140842 _26886 t)). Qed.
Lemma lem1140845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140846 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140845 (list _26886) Prop f x). Qed.
Lemma lem1140847 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term459 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (@lem1140846 _26886 (term458 _26886 _26887 P x) t). Qed.
Lemma lem1140848 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term457 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (TRANS (@lem1140843 _26886 _26887 P x t) (@lem1140847 _26886 _26887 P x t)). Qed.
Lemma lem1140849 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term81 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (TRANS (@lem1140837 _26886 _26887 P x t) (@lem1140848 _26886 _26887 P x t)). Qed.
Lemma lem1140850 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term321 _26886 _26887 P x t) = (term461 _26886 _26887 P x t).
Proof. exact (MK_COMB (@lem1140825) (@lem1140849 _26886 _26887 P x t)). Qed.
Lemma lem1140851 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term323 _26886 _26887 P t) = (term462 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1140850 _26886 _26887 P x t)). Qed.
Lemma lem1140852 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1140853 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term324 _26886 _26887 P t) = (term463 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140852 _26887) (@lem1140851 _26886 _26887 P t)). Qed.
Lemma lem1140854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140855 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term327 _26886 _26887 P t) = (term478 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1140854) (@lem1140853 _26886 _26887 P t)). Qed.
Lemma lem1140856 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term329 _26886 _26887 _18849 P t) = (term479 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140855 _26886 _26887 P t) (@lem1140824 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140857 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140862 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140863 {_26886 _26887 : Type'} (f : type740 _26886 _26887) (x : type1470 _26886 _26887) : (f x) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) f x).
Proof. exact (@lem1140862 (type1470 _26886 _26887) (_26886 -> Prop) f x). Qed.
Lemma lem1140865 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (_18849 P) = (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P).
Proof. exact (@lem1140863 _26886 _26887 _18849 P). Qed.
Lemma lem1140866 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140867 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term109 _26886 _26887 _18849 P) = (term447 _26886 _26887 _18849 P).
Proof. exact (MK_COMB (@lem1140857 _26886) (@lem1140865 _26886 _26887 _18849 P)). Qed.
Lemma lem1140868 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term448 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140867 _26886 _26887 _18849 P) (@lem1140866 _26886 t)). Qed.
Lemma lem1140870 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140871 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140870 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140872 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) : (term447 _26886 _26887 _18849 P) = (term449 _26886 _26887 _18849 P).
Proof. exact (@lem1140871 _26886 (@EX _26886) (@I ((_26887 -> _26886 -> Prop) -> _26886 -> Prop) _18849 P)). Qed.
Lemma lem1140873 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140874 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term450 _26886 _26887 _18849 P t).
Proof. exact (MK_COMB (@lem1140872 _26886 _26887 _18849 P) (@lem1140873 _26886 t)). Qed.
Lemma lem1140876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140877 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140876 (list _26886) Prop f x). Qed.
Lemma lem1140878 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term450 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (@lem1140877 _26886 (term449 _26886 _26887 _18849 P) t). Qed.
Lemma lem1140879 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term448 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140874 _26886 _26887 _18849 P t) (@lem1140878 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140880 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term110 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (TRANS (@lem1140868 _26886 _26887 _18849 P t) (@lem1140879 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140881 {_26886 : Type'} : (@EX _26886) = (@EX _26886).
Proof. exact (eq_refl (@EX _26886)). Qed.
Lemma lem1140886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140887 {_26886 _26887 : Type'} (f : type1470 _26886 _26887) (x : _26887) : (f x) = (@I (_26887 -> _26886 -> Prop) f x).
Proof. exact (@lem1140886 _26887 (_26886 -> Prop) f x). Qed.
Lemma lem1140889 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) : (P x') = (@I (_26887 -> _26886 -> Prop) P x').
Proof. exact (@lem1140887 _26886 _26887 P x'). Qed.
Lemma lem1140890 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140891 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) : (term455 _26886 _26887 P x') = (term456 _26886 _26887 P x').
Proof. exact (MK_COMB (@lem1140881 _26886) (@lem1140889 _26886 _26887 P x')). Qed.
Lemma lem1140892 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term81 _26886 _26887 P x' t) = (term457 _26886 _26887 P x' t).
Proof. exact (MK_COMB (@lem1140891 _26886 _26887 P x') (@lem1140890 _26886 t)). Qed.
Lemma lem1140894 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140895 {_26886 : Type'} (f : type663 _26886) (x : _26886 -> Prop) : (f x) = (@I ((_26886 -> Prop) -> (list _26886) -> Prop) f x).
Proof. exact (@lem1140894 (_26886 -> Prop) (type1143 _26886) f x). Qed.
Lemma lem1140896 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) : (term456 _26886 _26887 P x') = (term458 _26886 _26887 P x').
Proof. exact (@lem1140895 _26886 (@EX _26886) (@I (_26887 -> _26886 -> Prop) P x')). Qed.
Lemma lem1140897 {_26886 : Type'} (t : list _26886) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1140898 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term457 _26886 _26887 P x' t) = (term459 _26886 _26887 P x' t).
Proof. exact (MK_COMB (@lem1140896 _26886 _26887 P x') (@lem1140897 _26886 t)). Qed.
Lemma lem1140900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1140901 {_26886 : Type'} (f : type1143 _26886) (x : list _26886) : (f x) = (@I ((list _26886) -> Prop) f x).
Proof. exact (@lem1140900 (list _26886) Prop f x). Qed.
Lemma lem1140902 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term459 _26886 _26887 P x' t) = (term460 _26886 _26887 P x' t).
Proof. exact (@lem1140901 _26886 (term458 _26886 _26887 P x') t). Qed.
Lemma lem1140903 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term457 _26886 _26887 P x' t) = (term460 _26886 _26887 P x' t).
Proof. exact (TRANS (@lem1140898 _26886 _26887 P x' t) (@lem1140902 _26886 _26887 P x' t)). Qed.
Lemma lem1140904 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term81 _26886 _26887 P x' t) = (term460 _26886 _26887 P x' t).
Proof. exact (TRANS (@lem1140892 _26886 _26887 P x' t) (@lem1140903 _26886 _26887 P x' t)). Qed.
Lemma lem1140905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1140906 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term343 _26886 _26887 P x' t) = (term480 _26886 _26887 P x' t).
Proof. exact (MK_COMB (@lem1140905) (@lem1140904 _26886 _26887 P x' t)). Qed.
Lemma lem1140907 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term345 _26886 _26887 x' _18849 P t) = (term481 _26886 _26887 x' _18849 P t).
Proof. exact (MK_COMB (@lem1140906 _26886 _26887 P x' t) (@lem1140880 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1140909 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term362 _26886 _26887 x' _18849 P t) = (term482 _26886 _26887 x' _18849 P t).
Proof. exact (MK_COMB (@lem1140908) (@lem1140907 _26886 _26887 x' _18849 P t)). Qed.
Lemma lem1140910 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term364 _26886 _26887 x' _18849 P t) = (term483 _26886 _26887 x' _18849 P t).
Proof. exact (MK_COMB (@lem1140909 _26886 _26887 x' _18849 P t) (@lem1140856 _26886 _26887 _18849 P t)). Qed.
Lemma lem1140911 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term364 _26886 _26887 x' _18849 P t) : term483 _26886 _26887 x' _18849 P t.
Proof. exact (EQ_MP (@lem1140910 _26886 _26887 x' _18849 P t) (@lem1140594 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1141027 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term481 _26886 _26887 x' _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1141028 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term479 _26886 _26887 _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1141031 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term475 _26886 _26887 x h _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1141032 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term470 _26886 _26887 x h _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1141033 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term472 _26886 _26887 h _18849 P t.
Proof. exact (proj2 (@lem1141031 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141034 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term473 _26886 _26887 h P x t.
Proof. exact (proj1 (@lem1141031 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141039 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term454 _26886 _26887 x h _18849 P t.
Proof. exact (proj2 (@lem1141032 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141040 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term468 _26886 _26887 h P t.
Proof. exact (proj1 (@lem1141032 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141041 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term463 _26886 _26887 P t.
Proof. exact (proj2 (@lem1141040 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141046 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term463 _26886 _26887 P t.
Proof. exact (proj1 (@lem1141028 _26886 _26887 _18849 P t h1)). Qed.
Lemma lem1141047 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term475 _26886 _26887 x h _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1141048 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term470 _26886 _26887 x h _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1141049 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term472 _26886 _26887 h _18849 P t.
Proof. exact (proj2 (@lem1141047 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141050 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term473 _26886 _26887 h P x t.
Proof. exact (proj1 (@lem1141047 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141052 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term466 _26886 _26887 P h.
Proof. exact (proj1 (@lem1141049 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141055 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term454 _26886 _26887 x h _18849 P t.
Proof. exact (proj2 (@lem1141048 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141056 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term468 _26886 _26887 h P t.
Proof. exact (proj1 (@lem1141048 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141058 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term466 _26886 _26887 P h.
Proof. exact (proj1 (@lem1141056 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141303 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term461 _26886 _26887 P x t) = (term461 _26886 _26887 P x t).
Proof. exact (eq_refl (term461 _26886 _26887 P x t)). Qed.
Lemma lem1141304 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term462 _26886 _26887 P t) = (term462 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1141303 _26886 _26887 P x t)). Qed.
Lemma lem1141305 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1141307 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term463 _26886 _26887 P t) = (term463 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1141305 _26887) (@lem1141304 _26886 _26887 P t)). Qed.
Lemma lem1141308 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term463 _26886 _26887 P t.
Proof. exact (EQ_MP (@lem1141307 _26886 _26887 P t) (@lem1141041 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141389 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term461 _26886 _26887 P x t) = (term461 _26886 _26887 P x t).
Proof. exact (eq_refl (term461 _26886 _26887 P x t)). Qed.
Lemma lem1141390 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term462 _26886 _26887 P t) = (term462 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1141389 _26886 _26887 P x t)). Qed.
Lemma lem1141391 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1141393 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term463 _26886 _26887 P t) = (term463 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1141391 _26887) (@lem1141390 _26886 _26887 P t)). Qed.
Lemma lem1141394 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term463 _26886 _26887 P t.
Proof. exact (EQ_MP (@lem1141393 _26886 _26887 P t) (@lem1141041 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141471 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term464 _26886 _26887 P x h) = (term464 _26886 _26887 P x h).
Proof. exact (eq_refl (term464 _26886 _26887 P x h)). Qed.
Lemma lem1141472 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term465 _26886 _26887 P h) = (term465 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1141471 _26886 _26887 P x h)). Qed.
Lemma lem1141473 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1141475 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term466 _26886 _26887 P h) = (term466 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1141473 _26887) (@lem1141472 _26886 _26887 P h)). Qed.
Lemma lem1141476 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term466 _26886 _26887 P h.
Proof. exact (EQ_MP (@lem1141475 _26886 _26887 P h) (@lem1141052 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141484 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (h1). Qed.
Lemma lem1141546 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term461 _26886 _26887 P x t) = (term461 _26886 _26887 P x t).
Proof. exact (eq_refl (term461 _26886 _26887 P x t)). Qed.
Lemma lem1141547 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term462 _26886 _26887 P t) = (term462 _26886 _26887 P t).
Proof. exact (fun_ext (fun x : _26887 => @lem1141546 _26886 _26887 P x t)). Qed.
Lemma lem1141548 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1141550 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term463 _26886 _26887 P t) = (term463 _26886 _26887 P t).
Proof. exact (MK_COMB (@lem1141548 _26887) (@lem1141547 _26886 _26887 P t)). Qed.
Lemma lem1141551 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term463 _26886 _26887 P t.
Proof. exact (EQ_MP (@lem1141550 _26886 _26887 P t) (@lem1141046 _26886 _26887 _18849 P t h1)). Qed.
Lemma lem1141570 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term460 _26886 _26887 P x t) : term460 _26886 _26887 P x t.
Proof. exact (h1). Qed.
Lemma lem1141643 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term464 _26886 _26887 P x h) = (term464 _26886 _26887 P x h).
Proof. exact (eq_refl (term464 _26886 _26887 P x h)). Qed.
Lemma lem1141644 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term465 _26886 _26887 P h) = (term465 _26886 _26887 P h).
Proof. exact (fun_ext (fun x : _26887 => @lem1141643 _26886 _26887 P x h)). Qed.
Lemma lem1141645 {_26887 : Type'} : (@all _26887) = (@all _26887).
Proof. exact (eq_refl (@all _26887)). Qed.
Lemma lem1141647 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : (term466 _26886 _26887 P h) = (term466 _26886 _26887 P h).
Proof. exact (MK_COMB (@lem1141645 _26887) (@lem1141644 _26886 _26887 P h)). Qed.
Lemma lem1141648 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term466 _26886 _26887 P h.
Proof. exact (EQ_MP (@lem1141647 _26886 _26887 P h) (@lem1141058 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141659 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (h1). Qed.
Lemma lem1141748 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term451 _26886 _26887 _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1141803 {_26886 _26887 : Type'} (_18868 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term484 _26886 _26887 P t _18868.
Proof. exact (@lem1141308 _26886 _26887 x h _18849 P t h1 _18868). Qed.
Lemma lem1141804 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18868 : _26887) (t : list _26886) : (term484 _26886 _26887 P t _18868) = (term461 _26886 _26887 P _18868 t).
Proof. exact (eq_refl (term484 _26886 _26887 P t _18868)). Qed.
Lemma lem1141824 {_26886 _26887 : Type'} (_18875 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term484 _26886 _26887 P t _18875.
Proof. exact (@lem1141394 _26886 _26887 x h _18849 P t h1 _18875). Qed.
Lemma lem1141825 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18875 : _26887) (t : list _26886) : (term484 _26886 _26887 P t _18875) = (term461 _26886 _26887 P _18875 t).
Proof. exact (eq_refl (term484 _26886 _26887 P t _18875)). Qed.
Lemma lem1141845 {_26886 _26887 : Type'} (_18882 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term485 _26886 _26887 P h _18882.
Proof. exact (@lem1141476 _26886 _26887 x h _18849 P t h1 _18882). Qed.
Lemma lem1141846 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18882 : _26887) (h : _26886) : (term485 _26886 _26887 P h _18882) = (term464 _26886 _26887 P _18882 h).
Proof. exact (eq_refl (term485 _26886 _26887 P h _18882)). Qed.
Lemma lem1141863 {_26886 _26887 : Type'} (_18888 : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term484 _26886 _26887 P t _18888.
Proof. exact (@lem1141551 _26886 _26887 _18849 P t h1 _18888). Qed.
Lemma lem1141864 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18888 : _26887) (t : list _26886) : (term484 _26886 _26887 P t _18888) = (term461 _26886 _26887 P _18888 t).
Proof. exact (eq_refl (term484 _26886 _26887 P t _18888)). Qed.
Lemma lem1141887 {_26886 _26887 : Type'} (_18896 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term485 _26886 _26887 P h _18896.
Proof. exact (@lem1141648 _26886 _26887 x h _18849 P t h1 _18896). Qed.
Lemma lem1141888 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18896 : _26887) (h : _26886) : (term485 _26886 _26887 P h _18896) = (term464 _26886 _26887 P _18896 h).
Proof. exact (eq_refl (term485 _26886 _26887 P h _18896)). Qed.
Lemma lem1141936 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term471 _26886 _26887 _18849 P t.
Proof. exact (proj2 (@lem1141033 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141958 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term471 _26886 _26887 _18849 P t.
Proof. exact (proj2 (@lem1141033 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1141980 {_26886 _26887 : Type'} (_18868 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term461 _26886 _26887 P _18868 t.
Proof. exact (EQ_MP (@lem1141804 _26886 _26887 P _18868 t) (@lem1141803 _26886 _26887 _18868 x h _18849 P t h1)). Qed.
Lemma lem1142002 {_26886 _26887 : Type'} (_18875 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term461 _26886 _26887 P _18875 t.
Proof. exact (EQ_MP (@lem1141825 _26886 _26887 P _18875 t) (@lem1141824 _26886 _26887 _18875 x h _18849 P t h1)). Qed.
Lemma lem1142022 {_26886 _26887 : Type'} (_18882 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term464 _26886 _26887 P _18882 h.
Proof. exact (EQ_MP (@lem1141846 _26886 _26887 P _18882 h) (@lem1141845 _26886 _26887 _18882 x h _18849 P t h1)). Qed.
Lemma lem1142026 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (h1). Qed.
Lemma lem1142040 {_26886 _26887 : Type'} (_18888 : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term461 _26886 _26887 P _18888 t.
Proof. exact (EQ_MP (@lem1141864 _26886 _26887 P _18888 t) (@lem1141863 _26886 _26887 _18888 _18849 P t h1)). Qed.
Lemma lem1142048 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term460 _26886 _26887 P x t) : term460 _26886 _26887 P x t.
Proof. exact (h1). Qed.
Lemma lem1142066 {_26886 _26887 : Type'} (_18896 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term464 _26886 _26887 P _18896 h.
Proof. exact (EQ_MP (@lem1141888 _26886 _26887 P _18896 h) (@lem1141887 _26886 _26887 _18896 x h _18849 P t h1)). Qed.
Lemma lem1142070 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (h1). Qed.
Lemma lem1142086 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term471 _26886 _26887 _18849 P t.
Proof. exact (proj2 (@lem1141028 _26886 _26887 _18849 P t h1)). Qed.
Lemma lem1142092 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term451 _26886 _26887 _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1142094 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (proj2 (@lem1141027 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142095 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term486 _26886 _26887 _18849 P t.
Proof. exact (fun h0 : term471 _26886 _26887 _18849 P t => @lem1142094 _26886 _26887 x' _18849 P t h1). Qed.
Lemma lem1142097 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142098 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term486 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (@lem1142097 (term451 _26886 _26887 _18849 P t)). Qed.
Lemma lem1142099 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (EQ_MP (@lem1142098 _26886 _26887 _18849 P t) (@lem1142095 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142102 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142104 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term471 _26886 _26887 _18849 P t) = (term488 _26886 _26887 _18849 P t).
Proof. exact (@lem1142102 (term451 _26886 _26887 _18849 P t)). Qed.
Lemma lem1142107 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term488 _26886 _26887 _18849 P t.
Proof. exact (EQ_MP (@lem1142104 _26886 _26887 _18849 P t) (@lem1141936 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1142110 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : False.
Proof. exact (@lem1142107 _26886 _26887 x h _18849 P t h2 (@lem1142099 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142111 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : term489.
Proof. exact (fun h0 : ~ False => @lem1142110 _26886 _26887 x' x h _18849 P t h1 h2). Qed.
Lemma lem1142113 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142114 : term489 = False.
Proof. exact (@lem1142113 False). Qed.
Lemma lem1142115 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142114) (@lem1142111 _26886 _26887 x' x h _18849 P t h1 h2)). Qed.
Lemma lem1142117 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (proj2 (@lem1141027 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142118 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term486 _26886 _26887 _18849 P t.
Proof. exact (fun h0 : term471 _26886 _26887 _18849 P t => @lem1142117 _26886 _26887 x' _18849 P t h1). Qed.
Lemma lem1142120 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142121 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term486 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (@lem1142120 (term451 _26886 _26887 _18849 P t)). Qed.
Lemma lem1142122 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (EQ_MP (@lem1142121 _26886 _26887 _18849 P t) (@lem1142118 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142125 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142127 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term471 _26886 _26887 _18849 P t) = (term488 _26886 _26887 _18849 P t).
Proof. exact (@lem1142125 (term451 _26886 _26887 _18849 P t)). Qed.
Lemma lem1142130 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term488 _26886 _26887 _18849 P t.
Proof. exact (EQ_MP (@lem1142127 _26886 _26887 _18849 P t) (@lem1141958 _26886 _26887 x h _18849 P t h1)). Qed.
Lemma lem1142133 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : False.
Proof. exact (@lem1142130 _26886 _26887 x h _18849 P t h2 (@lem1142122 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142134 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : term489.
Proof. exact (fun h0 : ~ False => @lem1142133 _26886 _26887 x' x h _18849 P t h1 h2). Qed.
Lemma lem1142136 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142137 : term489 = False.
Proof. exact (@lem1142136 False). Qed.
Lemma lem1142138 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142137) (@lem1142134 _26886 _26887 x' x h _18849 P t h1 h2)). Qed.
Lemma lem1142140 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term460 _26886 _26887 P x' t.
Proof. exact (proj1 (@lem1141027 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142141 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term490 _26886 _26887 P x' t.
Proof. exact (fun h0 : term461 _26886 _26887 P x' t => @lem1142140 _26886 _26887 x' _18849 P t h1). Qed.
Lemma lem1142143 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142144 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term490 _26886 _26887 P x' t) = (term460 _26886 _26887 P x' t).
Proof. exact (@lem1142143 (term460 _26886 _26887 P x' t)). Qed.
Lemma lem1142145 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term460 _26886 _26887 P x' t.
Proof. exact (EQ_MP (@lem1142144 _26886 _26887 P x' t) (@lem1142141 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142148 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142150 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18868 : _26887) (t : list _26886) : (term461 _26886 _26887 P _18868 t) = (term491 _26886 _26887 P _18868 t).
Proof. exact (@lem1142148 (term460 _26886 _26887 P _18868 t)). Qed.
Lemma lem1142153 {_26886 _26887 : Type'} (_18868 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term491 _26886 _26887 P _18868 t.
Proof. exact (EQ_MP (@lem1142150 _26886 _26887 P _18868 t) (@lem1141980 _26886 _26887 _18868 x h _18849 P t h1)). Qed.
Lemma lem1142154 {_26886 _26887 : Type'} (_18868 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term491 _26886 _26887 P _18868 t.
Proof. exact (@lem1142153 _26886 _26887 _18868 x h _18849 P t h1). Qed.
Lemma lem1142155 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term491 _26886 _26887 P x' t.
Proof. exact (@lem1142154 _26886 _26887 x' x h _18849 P t h1). Qed.
Lemma lem1142158 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term481 _26886 _26887 x' _18849 P t) : False.
Proof. exact (@lem1142155 _26886 _26887 x' x h _18849 P t h1 (@lem1142145 _26886 _26887 x' _18849 P t h2)). Qed.
Lemma lem1142159 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term481 _26886 _26887 x' _18849 P t) : term489.
Proof. exact (fun h0 : ~ False => @lem1142158 _26886 _26887 x h x' _18849 P t h1 h2). Qed.
Lemma lem1142161 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142162 : term489 = False.
Proof. exact (@lem1142161 False). Qed.
Lemma lem1142163 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term481 _26886 _26887 x' _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142162) (@lem1142159 _26886 _26887 x h x' _18849 P t h1 h2)). Qed.
Lemma lem1142165 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term460 _26886 _26887 P x' t.
Proof. exact (proj1 (@lem1141027 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142166 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term490 _26886 _26887 P x' t.
Proof. exact (fun h0 : term461 _26886 _26887 P x' t => @lem1142165 _26886 _26887 x' _18849 P t h1). Qed.
Lemma lem1142168 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142169 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x' : _26887) (t : list _26886) : (term490 _26886 _26887 P x' t) = (term460 _26886 _26887 P x' t).
Proof. exact (@lem1142168 (term460 _26886 _26887 P x' t)). Qed.
Lemma lem1142170 {_26886 _26887 : Type'} (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) : term460 _26886 _26887 P x' t.
Proof. exact (EQ_MP (@lem1142169 _26886 _26887 P x' t) (@lem1142166 _26886 _26887 x' _18849 P t h1)). Qed.
Lemma lem1142173 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142175 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18875 : _26887) (t : list _26886) : (term461 _26886 _26887 P _18875 t) = (term491 _26886 _26887 P _18875 t).
Proof. exact (@lem1142173 (term460 _26886 _26887 P _18875 t)). Qed.
Lemma lem1142178 {_26886 _26887 : Type'} (_18875 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term491 _26886 _26887 P _18875 t.
Proof. exact (EQ_MP (@lem1142175 _26886 _26887 P _18875 t) (@lem1142002 _26886 _26887 _18875 x h _18849 P t h1)). Qed.
Lemma lem1142179 {_26886 _26887 : Type'} (_18875 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term491 _26886 _26887 P _18875 t.
Proof. exact (@lem1142178 _26886 _26887 _18875 x h _18849 P t h1). Qed.
Lemma lem1142180 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term491 _26886 _26887 P x' t.
Proof. exact (@lem1142179 _26886 _26887 x' x h _18849 P t h1). Qed.
Lemma lem1142183 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term481 _26886 _26887 x' _18849 P t) : False.
Proof. exact (@lem1142180 _26886 _26887 x' x h _18849 P t h1 (@lem1142170 _26886 _26887 x' _18849 P t h2)). Qed.
Lemma lem1142184 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term481 _26886 _26887 x' _18849 P t) : term489.
Proof. exact (fun h0 : ~ False => @lem1142183 _26886 _26887 x h x' _18849 P t h1 h2). Qed.
Lemma lem1142186 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142187 : term489 = False.
Proof. exact (@lem1142186 False). Qed.
Lemma lem1142188 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term481 _26886 _26887 x' _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142187) (@lem1142184 _26886 _26887 x h x' _18849 P t h1 h2)). Qed.
Lemma lem1142190 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (h1). Qed.
Lemma lem1142191 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term492 _26886 _26887 P x h.
Proof. exact (fun h0 : term464 _26886 _26887 P x h => @lem1142190 _26886 _26887 P x h h1). Qed.
Lemma lem1142193 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142194 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term492 _26886 _26887 P x h) = (term452 _26886 _26887 P x h).
Proof. exact (@lem1142193 (term452 _26886 _26887 P x h)). Qed.
Lemma lem1142195 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (EQ_MP (@lem1142194 _26886 _26887 P x h) (@lem1142191 _26886 _26887 P x h h1)). Qed.
Lemma lem1142198 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142200 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18882 : _26887) (h : _26886) : (term464 _26886 _26887 P _18882 h) = (term493 _26886 _26887 P _18882 h).
Proof. exact (@lem1142198 (term452 _26886 _26887 P _18882 h)). Qed.
Lemma lem1142203 {_26886 _26887 : Type'} (_18882 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term493 _26886 _26887 P _18882 h.
Proof. exact (EQ_MP (@lem1142200 _26886 _26887 P _18882 h) (@lem1142022 _26886 _26887 _18882 x h _18849 P t h1)). Qed.
Lemma lem1142204 {_26886 _26887 : Type'} (_18882 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term493 _26886 _26887 P _18882 h.
Proof. exact (@lem1142203 _26886 _26887 _18882 x h _18849 P t h1). Qed.
Lemma lem1142205 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term475 _26886 _26887 x h _18849 P t) : term493 _26886 _26887 P x h.
Proof. exact (@lem1142204 _26886 _26887 x x h _18849 P t h1). Qed.
Lemma lem1142208 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (@lem1142205 _26886 _26887 x h _18849 P t h1 (@lem1142195 _26886 _26887 P x h h2)). Qed.
Lemma lem1142209 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : term489.
Proof. exact (fun h0 : ~ False => @lem1142208 _26886 _26887 _18849 t P x h h1 h2). Qed.
Lemma lem1142211 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142212 : term489 = False.
Proof. exact (@lem1142211 False). Qed.
Lemma lem1142213 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142212) (@lem1142209 _26886 _26887 _18849 t P x h h1 h2)). Qed.
Lemma lem1142215 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term460 _26886 _26887 P x t) : term460 _26886 _26887 P x t.
Proof. exact (h1). Qed.
Lemma lem1142216 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term460 _26886 _26887 P x t) : term490 _26886 _26887 P x t.
Proof. exact (fun h0 : term461 _26886 _26887 P x t => @lem1142215 _26886 _26887 P x t h1). Qed.
Lemma lem1142218 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142219 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) : (term490 _26886 _26887 P x t) = (term460 _26886 _26887 P x t).
Proof. exact (@lem1142218 (term460 _26886 _26887 P x t)). Qed.
Lemma lem1142220 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term460 _26886 _26887 P x t) : term460 _26886 _26887 P x t.
Proof. exact (EQ_MP (@lem1142219 _26886 _26887 P x t) (@lem1142216 _26886 _26887 P x t h1)). Qed.
Lemma lem1142223 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142225 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18888 : _26887) (t : list _26886) : (term461 _26886 _26887 P _18888 t) = (term491 _26886 _26887 P _18888 t).
Proof. exact (@lem1142223 (term460 _26886 _26887 P _18888 t)). Qed.
Lemma lem1142228 {_26886 _26887 : Type'} (_18888 : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term491 _26886 _26887 P _18888 t.
Proof. exact (EQ_MP (@lem1142225 _26886 _26887 P _18888 t) (@lem1142040 _26886 _26887 _18888 _18849 P t h1)). Qed.
Lemma lem1142229 {_26886 _26887 : Type'} (_18888 : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term491 _26886 _26887 P _18888 t.
Proof. exact (@lem1142228 _26886 _26887 _18888 _18849 P t h1). Qed.
Lemma lem1142230 {_26886 _26887 : Type'} (x : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term491 _26886 _26887 P x t.
Proof. exact (@lem1142229 _26886 _26887 x _18849 P t h1). Qed.
Lemma lem1142233 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : False.
Proof. exact (@lem1142230 _26886 _26887 x _18849 P t h1 (@lem1142220 _26886 _26887 P x t h2)). Qed.
Lemma lem1142234 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : term489.
Proof. exact (fun h0 : ~ False => @lem1142233 _26886 _26887 _18849 P x t h1 h2). Qed.
Lemma lem1142236 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142237 : term489 = False.
Proof. exact (@lem1142236 False). Qed.
Lemma lem1142238 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : False.
Proof. exact (EQ_MP (@lem1142237) (@lem1142234 _26886 _26887 _18849 P x t h1 h2)). Qed.
Lemma lem1142240 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (h1). Qed.
Lemma lem1142241 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term492 _26886 _26887 P x h.
Proof. exact (fun h0 : term464 _26886 _26887 P x h => @lem1142240 _26886 _26887 P x h h1). Qed.
Lemma lem1142243 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142244 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) : (term492 _26886 _26887 P x h) = (term452 _26886 _26887 P x h).
Proof. exact (@lem1142243 (term452 _26886 _26887 P x h)). Qed.
Lemma lem1142245 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term452 _26886 _26887 P x h) : term452 _26886 _26887 P x h.
Proof. exact (EQ_MP (@lem1142244 _26886 _26887 P x h) (@lem1142241 _26886 _26887 P x h h1)). Qed.
Lemma lem1142248 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142250 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (_18896 : _26887) (h : _26886) : (term464 _26886 _26887 P _18896 h) = (term493 _26886 _26887 P _18896 h).
Proof. exact (@lem1142248 (term452 _26886 _26887 P _18896 h)). Qed.
Lemma lem1142253 {_26886 _26887 : Type'} (_18896 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term493 _26886 _26887 P _18896 h.
Proof. exact (EQ_MP (@lem1142250 _26886 _26887 P _18896 h) (@lem1142066 _26886 _26887 _18896 x h _18849 P t h1)). Qed.
Lemma lem1142254 {_26886 _26887 : Type'} (_18896 : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term493 _26886 _26887 P _18896 h.
Proof. exact (@lem1142253 _26886 _26887 _18896 x h _18849 P t h1). Qed.
Lemma lem1142255 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) : term493 _26886 _26887 P x h.
Proof. exact (@lem1142254 _26886 _26887 x x h _18849 P t h1). Qed.
Lemma lem1142258 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (@lem1142255 _26886 _26887 x h _18849 P t h1 (@lem1142245 _26886 _26887 P x h h2)). Qed.
Lemma lem1142259 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : term489.
Proof. exact (fun h0 : ~ False => @lem1142258 _26886 _26887 _18849 t P x h h1 h2). Qed.
Lemma lem1142261 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142262 : term489 = False.
Proof. exact (@lem1142261 False). Qed.
Lemma lem1142263 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142262) (@lem1142259 _26886 _26887 _18849 t P x h h1 h2)). Qed.
Lemma lem1142265 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term451 _26886 _26887 _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (h1). Qed.
Lemma lem1142266 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term451 _26886 _26887 _18849 P t) : term486 _26886 _26887 _18849 P t.
Proof. exact (fun h0 : term471 _26886 _26887 _18849 P t => @lem1142265 _26886 _26887 _18849 P t h1). Qed.
Lemma lem1142268 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142269 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term486 _26886 _26887 _18849 P t) = (term451 _26886 _26887 _18849 P t).
Proof. exact (@lem1142268 (term451 _26886 _26887 _18849 P t)). Qed.
Lemma lem1142270 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term451 _26886 _26887 _18849 P t) : term451 _26886 _26887 _18849 P t.
Proof. exact (EQ_MP (@lem1142269 _26886 _26887 _18849 P t) (@lem1142266 _26886 _26887 _18849 P t h1)). Qed.
Lemma lem1142273 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1142275 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) : (term471 _26886 _26887 _18849 P t) = (term488 _26886 _26887 _18849 P t).
Proof. exact (@lem1142273 (term451 _26886 _26887 _18849 P t)). Qed.
Lemma lem1142278 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) : term488 _26886 _26887 _18849 P t.
Proof. exact (EQ_MP (@lem1142275 _26886 _26887 _18849 P t) (@lem1142086 _26886 _26887 _18849 P t h1)). Qed.
Lemma lem1142281 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : False.
Proof. exact (@lem1142278 _26886 _26887 _18849 P t h1 (@lem1142270 _26886 _26887 _18849 P t h2)). Qed.
Lemma lem1142282 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : term489.
Proof. exact (fun h0 : ~ False => @lem1142281 _26886 _26887 _18849 P t h1 h2). Qed.
Lemma lem1142284 (p : Prop) : (term487 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1142285 : term489 = False.
Proof. exact (@lem1142284 False). Qed.
Lemma lem1142286 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142285) (@lem1142282 _26886 _26887 _18849 P t h1 h2)). Qed.
Lemma lem1142287 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : (term451 _26886 _26887 _18849 P t) = False.
Proof. exact (prop_ext (fun h3 : term451 _26886 _26887 _18849 P t => @lem1142286 _26886 _26887 _18849 P t h1 h2) (fun h3 : False => @lem1142092 _26886 _26887 _18849 P t h2)). Qed.
Lemma lem1142288 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142287 _26886 _26887 _18849 P t h1 h2) (@lem1142092 _26886 _26887 _18849 P t h2)). Qed.
Lemma lem1142289 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : (term452 _26886 _26887 P x h) = False.
Proof. exact (prop_ext (fun h3 : term452 _26886 _26887 P x h => @lem1142263 _26886 _26887 _18849 t P x h h1 h2) (fun h3 : False => @lem1142070 _26886 _26887 P x h h2)). Qed.
Lemma lem1142290 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142289 _26886 _26887 _18849 t P x h h1 h2) (@lem1142070 _26886 _26887 P x h h2)). Qed.
Lemma lem1142291 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : (term460 _26886 _26887 P x t) = False.
Proof. exact (prop_ext (fun h3 : term460 _26886 _26887 P x t => @lem1142238 _26886 _26887 _18849 P x t h1 h2) (fun h3 : False => @lem1142048 _26886 _26887 P x t h2)). Qed.
Lemma lem1142292 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : False.
Proof. exact (EQ_MP (@lem1142291 _26886 _26887 _18849 P x t h1 h2) (@lem1142048 _26886 _26887 P x t h2)). Qed.
Lemma lem1142293 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : (term452 _26886 _26887 P x h) = False.
Proof. exact (prop_ext (fun h3 : term452 _26886 _26887 P x h => @lem1142213 _26886 _26887 _18849 t P x h h1 h2) (fun h3 : False => @lem1142026 _26886 _26887 P x h h2)). Qed.
Lemma lem1142294 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142293 _26886 _26887 _18849 t P x h h1 h2) (@lem1142026 _26886 _26887 P x h h2)). Qed.
Lemma lem1142295 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : (term451 _26886 _26887 _18849 P t) = False.
Proof. exact (prop_ext (fun h3 : term451 _26886 _26887 _18849 P t => @lem1142288 _26886 _26887 _18849 P t h1 h2) (fun h3 : False => @lem1141748 _26886 _26887 _18849 P t h2)). Qed.
Lemma lem1142296 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142295 _26886 _26887 _18849 P t h1 h2) (@lem1141748 _26886 _26887 _18849 P t h2)). Qed.
Lemma lem1142297 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : (term452 _26886 _26887 P x h) = False.
Proof. exact (prop_ext (fun h3 : term452 _26886 _26887 P x h => @lem1142290 _26886 _26887 _18849 t P x h h1 h2) (fun h3 : False => @lem1141659 _26886 _26887 P x h h2)). Qed.
Lemma lem1142298 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142297 _26886 _26887 _18849 t P x h h1 h2) (@lem1141659 _26886 _26887 P x h h2)). Qed.
Lemma lem1142299 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : (term460 _26886 _26887 P x t) = False.
Proof. exact (prop_ext (fun h3 : term460 _26886 _26887 P x t => @lem1142292 _26886 _26887 _18849 P x t h1 h2) (fun h3 : False => @lem1141570 _26886 _26887 P x t h2)). Qed.
Lemma lem1142300 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : False.
Proof. exact (EQ_MP (@lem1142299 _26886 _26887 _18849 P x t h1 h2) (@lem1141570 _26886 _26887 P x t h2)). Qed.
Lemma lem1142301 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : (term452 _26886 _26887 P x h) = False.
Proof. exact (prop_ext (fun h3 : term452 _26886 _26887 P x h => @lem1142294 _26886 _26887 _18849 t P x h h1 h2) (fun h3 : False => @lem1141484 _26886 _26887 P x h h2)). Qed.
Lemma lem1142302 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142301 _26886 _26887 _18849 t P x h h1 h2) (@lem1141484 _26886 _26887 P x h h2)). Qed.
Lemma lem1142303 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : (term451 _26886 _26887 _18849 P t) = False.
Proof. exact (prop_ext (fun h3 : term451 _26886 _26887 _18849 P t => @lem1142296 _26886 _26887 _18849 P t h1 h2) (fun h3 : False => @lem1141748 _26886 _26887 _18849 P t h2)). Qed.
Lemma lem1142304 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term451 _26886 _26887 _18849 P t) : False.
Proof. exact (EQ_MP (@lem1142303 _26886 _26887 _18849 P t h1 h2) (@lem1141748 _26886 _26887 _18849 P t h2)). Qed.
Lemma lem1142305 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : (term452 _26886 _26887 P x h) = False.
Proof. exact (prop_ext (fun h3 : term452 _26886 _26887 P x h => @lem1142298 _26886 _26887 _18849 t P x h h1 h2) (fun h3 : False => @lem1141659 _26886 _26887 P x h h2)). Qed.
Lemma lem1142306 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142305 _26886 _26887 _18849 t P x h h1 h2) (@lem1141659 _26886 _26887 P x h h2)). Qed.
Lemma lem1142307 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : (term460 _26886 _26887 P x t) = False.
Proof. exact (prop_ext (fun h3 : term460 _26886 _26887 P x t => @lem1142300 _26886 _26887 _18849 P x t h1 h2) (fun h3 : False => @lem1141570 _26886 _26887 P x t h2)). Qed.
Lemma lem1142308 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (x : _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term460 _26886 _26887 P x t) : False.
Proof. exact (EQ_MP (@lem1142307 _26886 _26887 _18849 P x t h1 h2) (@lem1141570 _26886 _26887 P x t h2)). Qed.
Lemma lem1142309 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : (term452 _26886 _26887 P x h) = False.
Proof. exact (prop_ext (fun h3 : term452 _26886 _26887 P x h => @lem1142302 _26886 _26887 _18849 t P x h h1 h2) (fun h3 : False => @lem1141484 _26886 _26887 P x h h2)). Qed.
Lemma lem1142310 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (t : list _26886) (P : type1470 _26886 _26887) (x : _26887) (h : _26886) (h1 : term475 _26886 _26887 x h _18849 P t) (h2 : term452 _26886 _26887 P x h) : False.
Proof. exact (EQ_MP (@lem1142309 _26886 _26887 _18849 t P x h h1 h2) (@lem1141484 _26886 _26887 P x h h2)). Qed.
Lemma lem1142311 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term470 _26886 _26887 x h _18849 P t) : False.
Proof. exact (or_elim (@lem1141055 _26886 _26887 x h _18849 P t h2) (fun h0 : term452 _26886 _26887 P x h => @lem1142306 _26886 _26887 _18849 t P x h h2 h0) (fun h0 : term451 _26886 _26887 _18849 P t => @lem1142304 _26886 _26887 _18849 P t h1 h0)). Qed.
Lemma lem1142312 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : False.
Proof. exact (or_elim (@lem1141050 _26886 _26887 x h _18849 P t h2) (fun h0 : term452 _26886 _26887 P x h => @lem1142310 _26886 _26887 _18849 t P x h h2 h0) (fun h0 : term460 _26886 _26887 P x t => @lem1142308 _26886 _26887 _18849 P x t h1 h0)). Qed.
Lemma lem1142313 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term479 _26886 _26887 _18849 P t) (h2 : term443 _26886 _26887 x h _18849 P t) : False.
Proof. exact (or_elim (@lem1140798 _26886 _26887 x h _18849 P t h2) (fun h0 : term475 _26886 _26887 x h _18849 P t => @lem1142312 _26886 _26887 x h _18849 P t h1 h0) (fun h0 : term470 _26886 _26887 x h _18849 P t => @lem1142311 _26886 _26887 x h _18849 P t h1 h0)). Qed.
Lemma lem1142314 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (x' : _26887) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term470 _26886 _26887 x h _18849 P t) (h2 : term481 _26886 _26887 x' _18849 P t) : False.
Proof. exact (or_elim (@lem1141039 _26886 _26887 x h _18849 P t h1) (fun h0 : term452 _26886 _26887 P x h => @lem1142163 _26886 _26887 x h x' _18849 P t h1 h2) (fun h0 : term451 _26886 _26887 _18849 P t => @lem1142188 _26886 _26887 x h x' _18849 P t h1 h2)). Qed.
Lemma lem1142315 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term475 _26886 _26887 x h _18849 P t) : False.
Proof. exact (or_elim (@lem1141034 _26886 _26887 x h _18849 P t h2) (fun h0 : term452 _26886 _26887 P x h => @lem1142115 _26886 _26887 x' x h _18849 P t h1 h2) (fun h0 : term460 _26886 _26887 P x t => @lem1142138 _26886 _26887 x' x h _18849 P t h1 h2)). Qed.
Lemma lem1142316 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term481 _26886 _26887 x' _18849 P t) (h2 : term443 _26886 _26887 x h _18849 P t) : False.
Proof. exact (or_elim (@lem1140798 _26886 _26887 x h _18849 P t h2) (fun h0 : term475 _26886 _26887 x h _18849 P t => @lem1142315 _26886 _26887 x' x h _18849 P t h1 h0) (fun h0 : term470 _26886 _26887 x h _18849 P t => @lem1142314 _26886 _26887 x h x' _18849 P t h0 h1)). Qed.
Lemma lem1142317 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term364 _26886 _26887 x' _18849 P t) (h2 : term443 _26886 _26887 x h _18849 P t) : False.
Proof. exact (or_elim (@lem1140911 _26886 _26887 x' _18849 P t h1) (fun h0 : term481 _26886 _26887 x' _18849 P t => @lem1142316 _26886 _26887 x' x h _18849 P t h0 h2) (fun h0 : term479 _26886 _26887 _18849 P t => @lem1142313 _26886 _26887 x h _18849 P t h0 h2)). Qed.
Lemma lem1142318 {_26886 _26887 : Type'} (x' : _26887) (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term164 _26886 _26887 _18849) (h2 : term364 _26886 _26887 x' _18849 P t) (h3 : term443 _26886 _26887 x h _18849 P t) : False.
Proof. exact (ex_elim (@lem1140263 _26886 _26887 _18849 h1) (fun x'' : type739 _26886 _26887 => fun h0 : term316 _26886 _26887 _18849 x'' => @lem1142317 _26886 _26887 x' x h _18849 P t h2 h3)). Qed.
Lemma lem1142319 {_26886 _26887 : Type'} (x : _26887) (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term164 _26886 _26887 _18849) (h2 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) (h3 : term443 _26886 _26887 x h _18849 P t) : False.
Proof. exact (ex_elim (@lem1140356 _26886 _26887 _18849 P t h2) (fun x' : _26887 => fun h0 : term366 _26886 _26887 _18849 P t x' => @lem1142318 _26886 _26887 x' x h _18849 P t h1 h0 h3)). Qed.
Lemma lem1142320 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term164 _26886 _26887 _18849) (h2 : term170 _26886 _26887 h _18849 P t) (h3 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) : False.
Proof. exact (ex_elim (@lem1140592 _26886 _26887 h _18849 P t h2) (fun x : _26887 => fun h0 : term445 _26886 _26887 h _18849 P t x => @lem1142319 _26886 _26887 x h _18849 P t h1 h3 h0)). Qed.
Lemma lem1142321 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term164 _26886 _26887 _18849) (h2 : term170 _26886 _26887 h _18849 P t) (h3 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) : (term170 _26886 _26887 h _18849 P t) = False.
Proof. exact (prop_ext (fun h4 : term170 _26886 _26887 h _18849 P t => @lem1142320 _26886 _26887 h _18849 P t h1 h2 h3) (fun h4 : False => @lem1139837 _26886 _26887 h _18849 P t h2)). Qed.
Lemma lem1142322 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term164 _26886 _26887 _18849) (h2 : term170 _26886 _26887 h _18849 P t) (h3 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) : False.
Proof. exact (EQ_MP (@lem1142321 _26886 _26887 h _18849 P t h1 h2 h3) (@lem1139837 _26886 _26887 h _18849 P t h2)). Qed.
Lemma lem1142323 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term164 _26886 _26887 _18849) (h2 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) : term169 _26886 _26887 h _18849 P t.
Proof. exact (fun h0 : term170 _26886 _26887 h _18849 P t => @lem1142322 _26886 _26887 h _18849 P t h1 h0 h2). Qed.
Lemma lem1142324 {_26886 _26887 : Type'} (h : _26886) (_18849 : type740 _26886 _26887) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term164 _26886 _26887 _18849) (h2 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t)) : (term90 _26886 _26887 h P t) = (term111 _26886 _26887 h _18849 P t).
Proof. exact (EQ_MP (@lem1139836 _26886 _26887 h _18849 P t) (@lem1142323 _26886 _26887 h _18849 P t h1 h2)). Qed.
Lemma lem1142325 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : term164 _26886 _26887 _18849) : term114 _26886 _26887 h _18849 P t.
Proof. exact (fun h0 : (term9 _26886 _26887 P t) = (term110 _26886 _26887 _18849 P t) => @lem1142324 _26886 _26887 h _18849 P t h1 h0). Qed.
Lemma lem1142330 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : term164 _26886 _26887 _18849) : term116 _26886 _26887 _18849 P t.
Proof. exact (fun h : _26886 => @lem1142325 _26886 _26887 h P t _18849 h1). Qed.
Lemma lem1142335 {_26886 _26887 : Type'} (t : list _26886) (_18849 : type740 _26886 _26887) (h1 : term164 _26886 _26887 _18849) : term118 _26886 _26887 _18849 t.
Proof. exact (fun P : type1470 _26886 _26887 => @lem1142330 _26886 _26887 P t _18849 h1). Qed.
Lemma lem1142340 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) (h1 : term164 _26886 _26887 _18849) : term120 _26886 _26887 _18849.
Proof. exact (fun t : list _26886 => @lem1142335 _26886 _26887 t _18849 h1). Qed.
Lemma lem1142341 {_26886 _26887 : Type'} (_18849 : type740 _26886 _26887) : term166 _26886 _26887 _18849.
Proof. exact (fun h0 : term164 _26886 _26887 _18849 => @lem1142340 _26886 _26887 _18849 h0). Qed.
Lemma lem1142346 {_26886 _26887 : Type'} : term168 _26886 _26887.
Proof. exact (fun _18849 : type740 _26886 _26887 => @lem1142341 _26886 _26887 _18849). Qed.
Lemma lem1142347 {_26886 _26887 : Type'} : term103 _26886 _26887.
Proof. exact (EQ_MP (@lem1139830 _26886 _26887) (@lem1142346 _26886 _26887)). Qed.
Lemma lem1142348 {_26886 _26887 : Type'} (t : list _26886) : term494 _26886 _26887 t.
Proof. exact (@lem1142347 _26886 _26887 t). Qed.
Lemma lem1142349 {_26886 _26887 : Type'} (t : list _26886) : (term494 _26886 _26887 t) = (term99 _26886 _26887 t).
Proof. exact (eq_refl (term494 _26886 _26887 t)). Qed.
Lemma lem1142350 {_26886 _26887 : Type'} (t : list _26886) : term99 _26886 _26887 t.
Proof. exact (EQ_MP (@lem1142349 _26886 _26887 t) (@lem1142348 _26886 _26887 t)). Qed.
Lemma lem1142351 {_26886 _26887 : Type'} (t : list _26886) (P : type1470 _26886 _26887) : term495 _26886 _26887 t P.
Proof. exact (@lem1142350 _26886 _26887 t P). Qed.
Lemma lem1142352 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : (term495 _26886 _26887 t P) = (term95 _26886 _26887 P t).
Proof. exact (eq_refl (term495 _26886 _26887 t P)). Qed.
Lemma lem1142353 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) : term95 _26886 _26887 P t.
Proof. exact (EQ_MP (@lem1142352 _26886 _26887 P t) (@lem1142351 _26886 _26887 t P)). Qed.
Lemma lem1142354 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (t : list _26886) (h : _26886) : term496 _26886 _26887 P t h.
Proof. exact (@lem1142353 _26886 _26887 P t h). Qed.
Lemma lem1142355 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : (term496 _26886 _26887 P t h) = (term65 _26886 _26887 h P t).
Proof. exact (eq_refl (term496 _26886 _26887 P t h)). Qed.
Lemma lem1142356 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : term65 _26886 _26887 h P t.
Proof. exact (EQ_MP (@lem1142355 _26886 _26887 h P t) (@lem1142354 _26886 _26887 P t h)). Qed.
Lemma lem1142358 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) : term65 _26886 _26887 h P t.
Proof. exact (@lem1139415 _26886 _26887 h P t (@lem1142356 _26886 _26887 h P t)). Qed.
Lemma lem1142359 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : term63 _26886 _26887 h P t.
Proof. exact (@lem1142358 _26886 _26887 h P t (@lem1139297 _26886 _26887 P t h1)). Qed.
Lemma lem1142360 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term64 _26886 _26887 h P t) (h2 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : False.
Proof. exact (@lem1142359 _26886 _26887 h P t h2 (@lem1139399 _26886 _26887 h P t h1)). Qed.
Lemma lem1142361 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term64 _26886 _26887 h P t) (h2 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : (term64 _26886 _26887 h P t) = False.
Proof. exact (prop_ext (fun h3 : term64 _26886 _26887 h P t => @lem1142360 _26886 _26887 h P t h1 h2) (fun h3 : False => @lem1139399 _26886 _26887 h P t h1)). Qed.
Lemma lem1142362 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : term64 _26886 _26887 h P t) (h2 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : False.
Proof. exact (EQ_MP (@lem1142361 _26886 _26887 h P t h1 h2) (@lem1139399 _26886 _26887 h P t h1)). Qed.
Lemma lem1142363 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : term63 _26886 _26887 h P t.
Proof. exact (fun h0 : term64 _26886 _26887 h P t => @lem1142362 _26886 _26887 h P t h0 h1). Qed.
Lemma lem1142364 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : (term47 _26886 _26887 h P t) = (term61 _26886 _26887 h P t).
Proof. exact (EQ_MP (@lem1139398 _26886 _26887 h P t) (@lem1142363 _26886 _26887 h P t h1)). Qed.
Lemma lem1142365 {_26886 _26887 : Type'} (h : _26886) (P : type1470 _26886 _26887) (t : list _26886) (h1 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t)) : (term14 _26886 _26887 P h t) = (term15 _26886 _26887 P h t).
Proof. exact (EQ_MP (@lem1139394 _26886 _26887 P h t) (@lem1142364 _26886 _26887 h P t h1)). Qed.
Lemma lem1142366 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) (t : list _26886) : term17 _26886 _26887 P h t.
Proof. exact (fun h0 : (term9 _26886 _26887 P t) = (term10 _26886 _26887 P t) => @lem1142365 _26886 _26887 h P t h0). Qed.
Lemma lem1142371 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) (h : _26886) : term21 _26886 _26887 P h.
Proof. exact (fun t : list _26886 => @lem1142366 _26886 _26887 P h t). Qed.
Lemma lem1142376 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : term25 _26886 _26887 P.
Proof. exact (fun h : _26886 => @lem1142371 _26886 _26887 P h). Qed.
Lemma lem1142377 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : term27 _26886 _26887 P.
Proof. exact (conj (@lem1139333 _26886 _26887 P) (@lem1142376 _26886 _26887 P)). Qed.
Lemma lem1142378 {_26886 _26887 : Type'} (P : type1470 _26886 _26887) : term32 _26886 _26887 P.
Proof. exact (@lem1139296 _26886 _26887 P (@lem1142377 _26886 _26887 P)). Qed.
Lemma lem1142383 {_26886 _26887 : Type'} : term497 _26886 _26887.
Proof. exact (fun P : type1470 _26886 _26887 => @lem1142378 _26886 _26887 P). Qed.
