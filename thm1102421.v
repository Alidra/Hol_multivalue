Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1102421_term_abbrevs.
Require Import thm1101982_spec.
Require Import thm1102352_spec.
Lemma lem1102353 {_25350 _25351 : Type'} : (term0 _25350 _25351) = (term1 _25350 _25351).
Proof. exact (eq_refl (term0 _25350 _25351)). Qed.
Lemma lem1102354 {_25350 _25351 : Type'} : term1 _25350 _25351.
Proof. exact (EQ_MP (@lem1102353 _25350 _25351) (@lem1101982 _25350 _25351)). Qed.
Lemma lem1102355 {_25350 _25351 : Type'} : term2 _25350 _25351.
Proof. exact (@lem1102354 _25350 _25351 term3). Qed.
Lemma lem1102356 {_25350 _25351 : Type'} : (term2 _25350 _25351) = (term4 _25350 _25351).
Proof. exact (eq_refl (term2 _25350 _25351)). Qed.
Lemma lem1102357 {_25350 _25351 : Type'} : term4 _25350 _25351.
Proof. exact (EQ_MP (@lem1102356 _25350 _25351) (@lem1102355 _25350 _25351)). Qed.
Lemma lem1102358 {_25350 _25351 : Type'} (h1 : (@ITLIST _25350 _25351) = (term5 _25350 _25351)) : (@ITLIST _25350 _25351) = (term5 _25350 _25351).
Proof. exact (h1). Qed.
Lemma lem1102359 {_25350 _25351 : Type'} (h1 : (@ITLIST _25350 _25351) = (term5 _25350 _25351)) : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (SYM (@lem1102358 _25350 _25351 h1)). Qed.
Lemma lem1102360 {_25350 _25351 : Type'} (h1 : (term5 _25350 _25351) = (@ITLIST _25350 _25351)) : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (h1). Qed.
Lemma lem1102361 {_25350 _25351 : Type'} (h1 : (term5 _25350 _25351) = (@ITLIST _25350 _25351)) : (@ITLIST _25350 _25351) = (term5 _25350 _25351).
Proof. exact (SYM (@lem1102360 _25350 _25351 h1)). Qed.
Lemma lem1102362 {_25350 _25351 : Type'} : ((@ITLIST _25350 _25351) = (term5 _25350 _25351)) = ((term5 _25350 _25351) = (@ITLIST _25350 _25351)).
Proof. exact (prop_ext (fun h1 : (@ITLIST _25350 _25351) = (term5 _25350 _25351) => @lem1102359 _25350 _25351 h1) (fun h1 : (term5 _25350 _25351) = (@ITLIST _25350 _25351) => @lem1102361 _25350 _25351 h1)). Qed.
Lemma lem1102365 {_25350 _25351 : Type'} : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (EQ_MP (@lem1102362 _25350 _25351) (@lem1102352 _25350 _25351)). Qed.
Lemma lem1102366 {_25350 _25351 : Type'} : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (@lem1102365 _25350 _25351). Qed.
Lemma lem1102367 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1102368 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term6 _25350 _25351 f) = (@ITLIST _25350 _25351 f).
Proof. exact (MK_COMB (@lem1102366 _25350 _25351) (@lem1102367 _25350 _25351 f)). Qed.
Lemma lem1102369 {_25351 : Type'} : (@nil _25351) = (@nil _25351).
Proof. exact (eq_refl (@nil _25351)). Qed.
Lemma lem1102370 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term7 _25350 _25351 f) = (@ITLIST _25350 _25351 f (@nil _25351)).
Proof. exact (MK_COMB (@lem1102368 _25350 _25351 f) (@lem1102369 _25351)). Qed.
Lemma lem1102371 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1102372 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) : (term8 _25350 _25351 f b) = (@ITLIST _25350 _25351 f (@nil _25351) b).
Proof. exact (MK_COMB (@lem1102370 _25350 _25351 f) (@lem1102371 _25350 b)). Qed.
Lemma lem1102373 {_25350 : Type'} : (@eq _25350) = (@eq _25350).
Proof. exact (eq_refl (@eq _25350)). Qed.
Lemma lem1102374 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) : (term9 _25350 _25351 f b) = (term10 _25350 _25351 f b).
Proof. exact (MK_COMB (@lem1102373 _25350) (@lem1102372 _25350 _25351 f b)). Qed.
Lemma lem1102375 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1102376 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) : ((term8 _25350 _25351 f b) = b) = ((@ITLIST _25350 _25351 f (@nil _25351) b) = b).
Proof. exact (MK_COMB (@lem1102374 _25350 _25351 f b) (@lem1102375 _25350 b)). Qed.
Lemma lem1102377 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term11 _25350 _25351 f) = (term12 _25350 _25351 f).
Proof. exact (fun_ext (fun b : _25350 => @lem1102376 _25350 _25351 f b)). Qed.
Lemma lem1102378 {_25350 : Type'} : (@all _25350) = (@all _25350).
Proof. exact (eq_refl (@all _25350)). Qed.
Lemma lem1102379 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term13 _25350 _25351 f) = (term14 _25350 _25351 f).
Proof. exact (MK_COMB (@lem1102378 _25350) (@lem1102377 _25350 _25351 f)). Qed.
Lemma lem1102380 {_25350 _25351 : Type'} : (term15 _25350 _25351) = (term16 _25350 _25351).
Proof. exact (fun_ext (fun f : type1467 _25350 _25351 => @lem1102379 _25350 _25351 f)). Qed.
Lemma lem1102381 {_25350 _25351 : Type'} : (@all (_25351 -> _25350 -> _25350)) = (@all (_25351 -> _25350 -> _25350)).
Proof. exact (eq_refl (@all (_25351 -> _25350 -> _25350))). Qed.
Lemma lem1102382 {_25350 _25351 : Type'} : (term17 _25350 _25351) = (term18 _25350 _25351).
Proof. exact (MK_COMB (@lem1102381 _25350 _25351) (@lem1102380 _25350 _25351)). Qed.
Lemma lem1102383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1102384 {_25350 _25351 : Type'} : (term19 _25350 _25351) = (term20 _25350 _25351).
Proof. exact (MK_COMB (@lem1102383) (@lem1102382 _25350 _25351)). Qed.
Lemma lem1102386 {_25350 _25351 : Type'} : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (EQ_MP (@lem1102362 _25350 _25351) (@lem1102352 _25350 _25351)). Qed.
Lemma lem1102387 {_25350 _25351 : Type'} : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (@lem1102386 _25350 _25351). Qed.
Lemma lem1102388 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1102389 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term6 _25350 _25351 f) = (@ITLIST _25350 _25351 f).
Proof. exact (MK_COMB (@lem1102387 _25350 _25351) (@lem1102388 _25350 _25351 f)). Qed.
Lemma lem1102390 {_25351 : Type'} (h : _25351) (t : list _25351) : (@cons _25351 h t) = (@cons _25351 h t).
Proof. exact (eq_refl (@cons _25351 h t)). Qed.
Lemma lem1102391 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (h : _25351) (t : list _25351) : (term21 _25350 _25351 f h t) = (term22 _25350 _25351 f h t).
Proof. exact (MK_COMB (@lem1102389 _25350 _25351 f) (@lem1102390 _25351 h t)). Qed.
Lemma lem1102392 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1102393 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (h : _25351) (t : list _25351) (b : _25350) : (term23 _25350 _25351 f h t b) = (term24 _25350 _25351 f h t b).
Proof. exact (MK_COMB (@lem1102391 _25350 _25351 f h t) (@lem1102392 _25350 b)). Qed.
Lemma lem1102394 {_25350 : Type'} : (@eq _25350) = (@eq _25350).
Proof. exact (eq_refl (@eq _25350)). Qed.
Lemma lem1102395 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (h : _25351) (t : list _25351) (b : _25350) : (term25 _25350 _25351 f h t b) = (term26 _25350 _25351 f h t b).
Proof. exact (MK_COMB (@lem1102394 _25350) (@lem1102393 _25350 _25351 f h t b)). Qed.
Lemma lem1102397 {_25350 _25351 : Type'} : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (EQ_MP (@lem1102362 _25350 _25351) (@lem1102352 _25350 _25351)). Qed.
Lemma lem1102398 {_25350 _25351 : Type'} : (term5 _25350 _25351) = (@ITLIST _25350 _25351).
Proof. exact (@lem1102397 _25350 _25351). Qed.
Lemma lem1102399 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1102400 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term6 _25350 _25351 f) = (@ITLIST _25350 _25351 f).
Proof. exact (MK_COMB (@lem1102398 _25350 _25351) (@lem1102399 _25350 _25351 f)). Qed.
Lemma lem1102401 {_25351 : Type'} (t : list _25351) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1102402 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (t : list _25351) : (term27 _25350 _25351 f t) = (@ITLIST _25350 _25351 f t).
Proof. exact (MK_COMB (@lem1102400 _25350 _25351 f) (@lem1102401 _25351 t)). Qed.
Lemma lem1102403 {_25350 : Type'} (b : _25350) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1102404 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : (term28 _25350 _25351 f t b) = (@ITLIST _25350 _25351 f t b).
Proof. exact (MK_COMB (@lem1102402 _25350 _25351 f t) (@lem1102403 _25350 b)). Qed.
Lemma lem1102405 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (h : _25351) : (f h) = (f h).
Proof. exact (eq_refl (f h)). Qed.
Lemma lem1102406 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : (term29 _25350 _25351 h f t b) = (term30 _25350 _25351 h f t b).
Proof. exact (MK_COMB (@lem1102405 _25350 _25351 f h) (@lem1102404 _25350 _25351 f t b)). Qed.
Lemma lem1102407 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : ((term23 _25350 _25351 f h t b) = (term29 _25350 _25351 h f t b)) = ((term24 _25350 _25351 f h t b) = (term30 _25350 _25351 h f t b)).
Proof. exact (MK_COMB (@lem1102395 _25350 _25351 f h t b) (@lem1102406 _25350 _25351 h f t b)). Qed.
Lemma lem1102408 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) : (term31 _25350 _25351 h f t) = (term32 _25350 _25351 h f t).
Proof. exact (fun_ext (fun b : _25350 => @lem1102407 _25350 _25351 h f t b)). Qed.
Lemma lem1102409 {_25350 : Type'} : (@all _25350) = (@all _25350).
Proof. exact (eq_refl (@all _25350)). Qed.
Lemma lem1102410 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) : (term33 _25350 _25351 h f t) = (term34 _25350 _25351 h f t).
Proof. exact (MK_COMB (@lem1102409 _25350) (@lem1102408 _25350 _25351 h f t)). Qed.
Lemma lem1102411 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) : (term35 _25350 _25351 h f) = (term36 _25350 _25351 h f).
Proof. exact (fun_ext (fun t : list _25351 => @lem1102410 _25350 _25351 h f t)). Qed.
Lemma lem1102412 {_25351 : Type'} : (@all (list _25351)) = (@all (list _25351)).
Proof. exact (eq_refl (@all (list _25351))). Qed.
Lemma lem1102413 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) : (term37 _25350 _25351 h f) = (term38 _25350 _25351 h f).
Proof. exact (MK_COMB (@lem1102412 _25351) (@lem1102411 _25350 _25351 h f)). Qed.
Lemma lem1102414 {_25350 _25351 : Type'} (h : _25351) : (term39 _25350 _25351 h) = (term40 _25350 _25351 h).
Proof. exact (fun_ext (fun f : type1467 _25350 _25351 => @lem1102413 _25350 _25351 h f)). Qed.
Lemma lem1102415 {_25350 _25351 : Type'} : (@all (_25351 -> _25350 -> _25350)) = (@all (_25351 -> _25350 -> _25350)).
Proof. exact (eq_refl (@all (_25351 -> _25350 -> _25350))). Qed.
Lemma lem1102416 {_25350 _25351 : Type'} (h : _25351) : (term41 _25350 _25351 h) = (term42 _25350 _25351 h).
Proof. exact (MK_COMB (@lem1102415 _25350 _25351) (@lem1102414 _25350 _25351 h)). Qed.
Lemma lem1102417 {_25350 _25351 : Type'} : (term43 _25350 _25351) = (term44 _25350 _25351).
Proof. exact (fun_ext (fun h : _25351 => @lem1102416 _25350 _25351 h)). Qed.
Lemma lem1102418 {_25351 : Type'} : (@all _25351) = (@all _25351).
Proof. exact (eq_refl (@all _25351)). Qed.
Lemma lem1102419 {_25350 _25351 : Type'} : (term45 _25350 _25351) = (term46 _25350 _25351).
Proof. exact (MK_COMB (@lem1102418 _25351) (@lem1102417 _25350 _25351)). Qed.
Lemma lem1102420 {_25350 _25351 : Type'} : (term4 _25350 _25351) = (term47 _25350 _25351).
Proof. exact (MK_COMB (@lem1102384 _25350 _25351) (@lem1102419 _25350 _25351)). Qed.
Lemma lem1102421 {_25350 _25351 : Type'} : term47 _25350 _25351.
Proof. exact (EQ_MP (@lem1102420 _25350 _25351) (@lem1102357 _25350 _25351)). Qed.
