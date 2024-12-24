Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import SUBSET_ANTISYM_EQ_spec.
Require Import SUBSET_CROSS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
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
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem4339282 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term0 A t s) = (s = t)) : (term0 A t s) = (s = t).
Proof. exact (h1). Qed.
Lemma lem4339283 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term0 A t s) = (s = t)) : (s = t) = (term0 A t s).
Proof. exact (SYM (@lem4339282 A s t h1)). Qed.
Lemma lem4339284 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term0 A t s)) : (s = t) = (term0 A t s).
Proof. exact (h1). Qed.
Lemma lem4339285 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term0 A t s)) : (term0 A t s) = (s = t).
Proof. exact (SYM (@lem4339284 A t s h1)). Qed.
Lemma lem4339286 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term0 A t s) = (s = t)) = ((s = t) = (term0 A t s)).
Proof. exact (prop_ext (fun h1 : (term0 A t s) = (s = t) => @lem4339283 A s t h1) (fun h1 : (s = t) = (term0 A t s) => @lem4339285 A t s h1)). Qed.
Lemma lem4339287 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4339286 A t s)). Qed.
Lemma lem4339288 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4339289 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (MK_COMB (@lem4339288 A) (@lem4339287 A s)). Qed.
Lemma lem4339290 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4339289 A s)). Qed.
Lemma lem4339291 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4339292 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4339291 A) (@lem4339290 A)). Qed.
Lemma lem4339293 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4339292 A) (@lem3219910 A)). Qed.
Lemma lem4339294 {_104190 _104196 : Type'} (s : _104190 -> Prop) : term9 _104190 _104196 s.
Proof. exact (@lem4339138 _104190 _104196 s). Qed.
Lemma lem4339295 {_104190 _104196 : Type'} (s : _104190 -> Prop) : (term9 _104190 _104196 s) = (term10 _104190 _104196 s).
Proof. exact (eq_refl (term9 _104190 _104196 s)). Qed.
Lemma lem4339296 {_104190 _104196 : Type'} (s : _104190 -> Prop) : term10 _104190 _104196 s.
Proof. exact (EQ_MP (@lem4339295 _104190 _104196 s) (@lem4339294 _104190 _104196 s)). Qed.
Lemma lem4339297 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : term11 _104190 _104196 s t.
Proof. exact (@lem4339296 _104190 _104196 s t). Qed.
Lemma lem4339298 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : (term11 _104190 _104196 s t) = (term12 _104190 _104196 s t).
Proof. exact (eq_refl (term11 _104190 _104196 s t)). Qed.
Lemma lem4339299 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) : term12 _104190 _104196 s t.
Proof. exact (EQ_MP (@lem4339298 _104190 _104196 s t) (@lem4339297 _104190 _104196 s t)). Qed.
Lemma lem4339300 {_104190 _104196 : Type'} (s : _104190 -> Prop) (t : _104196 -> Prop) (s' : _104190 -> Prop) : term13 _104190 _104196 s t s'.
Proof. exact (@lem4339299 _104190 _104196 s t s'). Qed.
Lemma lem4339301 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : (term13 _104190 _104196 s t s') = (term14 _104190 _104196 s s' t).
Proof. exact (eq_refl (term13 _104190 _104196 s t s')). Qed.
Lemma lem4339302 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) : term14 _104190 _104196 s s' t.
Proof. exact (EQ_MP (@lem4339301 _104190 _104196 s s' t) (@lem4339300 _104190 _104196 s t s')). Qed.
Lemma lem4339303 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : term15 _104190 _104196 s s' t t'.
Proof. exact (@lem4339302 _104190 _104196 s s' t t'). Qed.
Lemma lem4339304 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term15 _104190 _104196 s s' t t') = ((term16 _104190 _104196 s t s' t') = (term17 _104190 _104196 s s' t t')).
Proof. exact (eq_refl (term15 _104190 _104196 s s' t t')). Qed.
Lemma lem4339306 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (@lem4339293 A s). Qed.
Lemma lem4339307 {A : Type'} (s : A -> Prop) : (term18 A s) = (term4 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem4339308 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (EQ_MP (@lem4339307 A s) (@lem4339306 A s)). Qed.
Lemma lem4339309 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4339308 A s t). Qed.
Lemma lem4339310 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term19 A s t) = ((s = t) = (term0 A t s)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4339335 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339336 {A B : Type'} (t : type1210 A B) (s : type1210 A B) : (s = t) = (term20 A B t s).
Proof. exact (@lem4339335 (prod A B) t s). Qed.
Lemma lem4339337 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (t : B -> Prop) : ((@CROSS B A s t) = (@CROSS B A s' t')) = (term21 A B s' t' s t).
Proof. exact (@lem4339336 A B (@CROSS B A s' t') (@CROSS B A s t)). Qed.
Lemma lem4339341 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term16 _104190 _104196 s t s' t') = (term17 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4339304 _104190 _104196 s s' t t') (@lem4339303 _104190 _104196 s s' t t')). Qed.
Lemma lem4339342 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term16 A B s t s' t') = (term17 A B s s' t t').
Proof. exact (@lem4339341 A B s s' t t'). Qed.
Lemma lem4339348 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339349 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (@lem4339348 A t s). Qed.
Lemma lem4339350 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term22 A s).
Proof. exact (@lem4339349 A (@EMPTY A) s). Qed.
Lemma lem4339353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339354 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem4339353) (@lem4339350 A s)). Qed.
Lemma lem4339360 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339361 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (s = t) = (term0 B t s).
Proof. exact (@lem4339360 B t s). Qed.
Lemma lem4339362 {B : Type'} (t : B -> Prop) : (t = (@EMPTY B)) = (term22 B t).
Proof. exact (@lem4339361 B (@EMPTY B) t). Qed.
Lemma lem4339365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339366 {B : Type'} (t : B -> Prop) : (term23 B t) = (term24 B t).
Proof. exact (MK_COMB (@lem4339365) (@lem4339362 B t)). Qed.
Lemma lem4339369 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term25 A B s s' t t') = (term25 A B s s' t t').
Proof. exact (eq_refl (term25 A B s s' t t')). Qed.
Lemma lem4339370 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term26 A B s s' t t') = (term27 A B s s' t t').
Proof. exact (MK_COMB (@lem4339366 B t) (@lem4339369 A B s s' t t')). Qed.
Lemma lem4339373 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term17 A B s s' t t') = (term28 A B s s' t t').
Proof. exact (MK_COMB (@lem4339354 A s) (@lem4339370 A B s s' t t')). Qed.
Lemma lem4339376 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term16 A B s t s' t') = (term28 A B s s' t t').
Proof. exact (TRANS (@lem4339342 A B s s' t t') (@lem4339373 A B s s' t t')). Qed.
Lemma lem4339377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339378 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term29 A B s t s' t') = (term30 A B s s' t t').
Proof. exact (MK_COMB (@lem4339377) (@lem4339376 A B s s' t t')). Qed.
Lemma lem4339380 {_104190 _104196 : Type'} (s : _104190 -> Prop) (s' : _104190 -> Prop) (t : _104196 -> Prop) (t' : _104196 -> Prop) : (term16 _104190 _104196 s t s' t') = (term17 _104190 _104196 s s' t t').
Proof. exact (EQ_MP (@lem4339304 _104190 _104196 s s' t t') (@lem4339303 _104190 _104196 s s' t t')). Qed.
Lemma lem4339381 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term16 A B s t s' t') = (term17 A B s s' t t').
Proof. exact (@lem4339380 A B s s' t t'). Qed.
Lemma lem4339382 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term16 A B s' t' s t) = (term17 A B s' s t' t).
Proof. exact (@lem4339381 A B s' s t' t). Qed.
Lemma lem4339388 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339389 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (@lem4339388 A t s). Qed.
Lemma lem4339390 {A : Type'} (s' : A -> Prop) : (s' = (@EMPTY A)) = (term22 A s').
Proof. exact (@lem4339389 A (@EMPTY A) s'). Qed.
Lemma lem4339393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339394 {A : Type'} (s' : A -> Prop) : (term23 A s') = (term24 A s').
Proof. exact (MK_COMB (@lem4339393) (@lem4339390 A s')). Qed.
Lemma lem4339400 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339401 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (s = t) = (term0 B t s).
Proof. exact (@lem4339400 B t s). Qed.
Lemma lem4339402 {B : Type'} (t' : B -> Prop) : (t' = (@EMPTY B)) = (term22 B t').
Proof. exact (@lem4339401 B (@EMPTY B) t'). Qed.
Lemma lem4339405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339406 {B : Type'} (t' : B -> Prop) : (term23 B t') = (term24 B t').
Proof. exact (MK_COMB (@lem4339405) (@lem4339402 B t')). Qed.
Lemma lem4339409 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term25 A B s' s t' t) = (term25 A B s' s t' t).
Proof. exact (eq_refl (term25 A B s' s t' t)). Qed.
Lemma lem4339410 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term26 A B s' s t' t) = (term27 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339406 B t') (@lem4339409 A B s' s t' t)). Qed.
Lemma lem4339413 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term17 A B s' s t' t) = (term28 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339394 A s') (@lem4339410 A B s' s t' t)). Qed.
Lemma lem4339416 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term16 A B s' t' s t) = (term28 A B s' s t' t).
Proof. exact (TRANS (@lem4339382 A B s' s t' t) (@lem4339413 A B s' s t' t)). Qed.
Lemma lem4339417 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term21 A B s' t' s t) = (term31 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339378 A B s s' t t') (@lem4339416 A B s' s t' t)). Qed.
Lemma lem4339420 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((@CROSS B A s t) = (@CROSS B A s' t')) = (term31 A B s' s t' t).
Proof. exact (TRANS (@lem4339337 A B s' t' s t) (@lem4339417 A B s' s t' t)). Qed.
Lemma lem4339421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4339422 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term32 A B s t s' t') = (term33 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339421) (@lem4339420 A B s' s t' t)). Qed.
Lemma lem4339432 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339433 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (@lem4339432 A t s). Qed.
Lemma lem4339434 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term22 A s).
Proof. exact (@lem4339433 A (@EMPTY A) s). Qed.
Lemma lem4339437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339438 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A s).
Proof. exact (MK_COMB (@lem4339437) (@lem4339434 A s)). Qed.
Lemma lem4339442 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339443 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (s = t) = (term0 B t s).
Proof. exact (@lem4339442 B t s). Qed.
Lemma lem4339444 {B : Type'} (t : B -> Prop) : (t = (@EMPTY B)) = (term22 B t).
Proof. exact (@lem4339443 B (@EMPTY B) t). Qed.
Lemma lem4339447 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term34 A B s t) = (term35 A B s t).
Proof. exact (MK_COMB (@lem4339438 A s) (@lem4339444 B t)). Qed.
Lemma lem4339450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339451 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term36 A B s t) = (term37 A B s t).
Proof. exact (MK_COMB (@lem4339450) (@lem4339447 A B s t)). Qed.
Lemma lem4339457 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339458 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (@lem4339457 A t s). Qed.
Lemma lem4339459 {A : Type'} (s' : A -> Prop) : (s' = (@EMPTY A)) = (term22 A s').
Proof. exact (@lem4339458 A (@EMPTY A) s'). Qed.
Lemma lem4339462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339463 {A : Type'} (s' : A -> Prop) : (term23 A s') = (term24 A s').
Proof. exact (MK_COMB (@lem4339462) (@lem4339459 A s')). Qed.
Lemma lem4339467 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339468 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (s = t) = (term0 B t s).
Proof. exact (@lem4339467 B t s). Qed.
Lemma lem4339469 {B : Type'} (t' : B -> Prop) : (t' = (@EMPTY B)) = (term22 B t').
Proof. exact (@lem4339468 B (@EMPTY B) t'). Qed.
Lemma lem4339472 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term34 A B s' t') = (term35 A B s' t').
Proof. exact (MK_COMB (@lem4339463 A s') (@lem4339469 B t')). Qed.
Lemma lem4339475 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term38 A B s t s' t') = (term39 A B s t s' t').
Proof. exact (MK_COMB (@lem4339451 A B s t) (@lem4339472 A B s' t')). Qed.
Lemma lem4339478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339479 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term40 A B s t s' t') = (term41 A B s t s' t').
Proof. exact (MK_COMB (@lem4339478) (@lem4339475 A B s t s' t')). Qed.
Lemma lem4339485 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339486 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (@lem4339485 A t s). Qed.
Lemma lem4339487 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (s = s') = (term0 A s' s).
Proof. exact (@lem4339486 A s' s). Qed.
Lemma lem4339490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339491 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term42 A s s') = (term43 A s' s).
Proof. exact (MK_COMB (@lem4339490) (@lem4339487 A s' s)). Qed.
Lemma lem4339495 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4339310 A t s) (@lem4339309 A s t)). Qed.
Lemma lem4339496 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (s = t) = (term0 B t s).
Proof. exact (@lem4339495 B t s). Qed.
Lemma lem4339497 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (t = t') = (term0 B t' t).
Proof. exact (@lem4339496 B t' t). Qed.
Lemma lem4339500 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term44 A B s s' t t') = (term45 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339491 A s' s) (@lem4339497 B t' t)). Qed.
Lemma lem4339503 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term46 A B s s' t t') = (term47 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339479 A B s t s' t') (@lem4339500 A B s' s t' t)). Qed.
Lemma lem4339506 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (((@CROSS B A s t) = (@CROSS B A s' t')) = (term46 A B s s' t t')) = ((term31 A B s' s t' t) = (term47 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4339422 A B s' s t' t) (@lem4339503 A B s' s t' t)). Qed.
Lemma lem4339511 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term48 A B s s' t) = (term49 A B s' s t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem4339506 A B s' s t' t)). Qed.
Lemma lem4339512 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4339513 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term50 A B s s' t) = (term51 A B s' s t).
Proof. exact (MK_COMB (@lem4339512 B) (@lem4339511 A B s' s t)). Qed.
Lemma lem4339518 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term52 A B s s') = (term53 A B s' s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4339513 A B s' s t)). Qed.
Lemma lem4339519 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4339520 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term54 A B s s') = (term55 A B s' s).
Proof. exact (MK_COMB (@lem4339519 B) (@lem4339518 A B s' s)). Qed.
Lemma lem4339525 {A B : Type'} (s : A -> Prop) : (term56 A B s) = (term57 A B s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem4339520 A B s' s)). Qed.
Lemma lem4339526 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4339527 {A B : Type'} (s : A -> Prop) : (term58 A B s) = (term59 A B s).
Proof. exact (MK_COMB (@lem4339526 A) (@lem4339525 A B s)). Qed.
Lemma lem4339532 {A B : Type'} : (term60 A B) = (term61 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4339527 A B s)). Qed.
Lemma lem4339533 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4339534 {A B : Type'} : (term62 A B) = (term63 A B).
Proof. exact (MK_COMB (@lem4339533 A) (@lem4339532 A B)). Qed.
Lemma lem4339539 {A B : Type'} : (term63 A B) = (term62 A B).
Proof. exact (SYM (@lem4339534 A B)). Qed.
Lemma lem4339567 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339567 A s t). Qed.
Lemma lem4339569 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@EMPTY A)) = (term65 A s).
Proof. exact (@lem4339568 A s (@EMPTY A)). Qed.
Lemma lem4339576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339577 {A : Type'} (s : A -> Prop) : (term66 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem4339576) (@lem4339569 A s)). Qed.
Lemma lem4339579 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339580 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339579 A s t). Qed.
Lemma lem4339581 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (term68 A s).
Proof. exact (@lem4339580 A (@EMPTY A) s). Qed.
Lemma lem4339588 {A : Type'} (s : A -> Prop) : (term22 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem4339577 A s) (@lem4339581 A s)). Qed.
Lemma lem4339591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339592 {A : Type'} (s : A -> Prop) : (term24 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem4339591) (@lem4339588 A s)). Qed.
Lemma lem4339598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339599 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339598 B s t). Qed.
Lemma lem4339600 {B : Type'} (t : B -> Prop) : (@SUBSET B t (@EMPTY B)) = (term65 B t).
Proof. exact (@lem4339599 B t (@EMPTY B)). Qed.
Lemma lem4339607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339608 {B : Type'} (t : B -> Prop) : (term66 B t) = (term67 B t).
Proof. exact (MK_COMB (@lem4339607) (@lem4339600 B t)). Qed.
Lemma lem4339610 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339611 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339610 B s t). Qed.
Lemma lem4339612 {B : Type'} (t : B -> Prop) : (@SUBSET B (@EMPTY B) t) = (term68 B t).
Proof. exact (@lem4339611 B (@EMPTY B) t). Qed.
Lemma lem4339619 {B : Type'} (t : B -> Prop) : (term22 B t) = (term69 B t).
Proof. exact (MK_COMB (@lem4339608 B t) (@lem4339612 B t)). Qed.
Lemma lem4339622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339623 {B : Type'} (t : B -> Prop) : (term24 B t) = (term70 B t).
Proof. exact (MK_COMB (@lem4339622) (@lem4339619 B t)). Qed.
Lemma lem4339627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339627 A s t). Qed.
Lemma lem4339629 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (@SUBSET A s s') = (term64 A s s').
Proof. exact (@lem4339628 A s s'). Qed.
Lemma lem4339636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339637 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term71 A s s') = (term72 A s s').
Proof. exact (MK_COMB (@lem4339636) (@lem4339629 A s s')). Qed.
Lemma lem4339639 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339640 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339639 B s t). Qed.
Lemma lem4339641 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (@SUBSET B t t') = (term64 B t t').
Proof. exact (@lem4339640 B t t'). Qed.
Lemma lem4339648 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term25 A B s s' t t') = (term73 A B s s' t t').
Proof. exact (MK_COMB (@lem4339637 A s s') (@lem4339641 B t t')). Qed.
Lemma lem4339651 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term27 A B s s' t t') = (term74 A B s s' t t').
Proof. exact (MK_COMB (@lem4339623 B t) (@lem4339648 A B s s' t t')). Qed.
Lemma lem4339654 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term28 A B s s' t t') = (term75 A B s s' t t').
Proof. exact (MK_COMB (@lem4339592 A s) (@lem4339651 A B s s' t t')). Qed.
Lemma lem4339657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339658 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term30 A B s s' t t') = (term76 A B s s' t t').
Proof. exact (MK_COMB (@lem4339657) (@lem4339654 A B s s' t t')). Qed.
Lemma lem4339664 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339665 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339664 A s t). Qed.
Lemma lem4339666 {A : Type'} (s' : A -> Prop) : (@SUBSET A s' (@EMPTY A)) = (term65 A s').
Proof. exact (@lem4339665 A s' (@EMPTY A)). Qed.
Lemma lem4339673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339674 {A : Type'} (s' : A -> Prop) : (term66 A s') = (term67 A s').
Proof. exact (MK_COMB (@lem4339673) (@lem4339666 A s')). Qed.
Lemma lem4339676 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339677 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339676 A s t). Qed.
Lemma lem4339678 {A : Type'} (s' : A -> Prop) : (@SUBSET A (@EMPTY A) s') = (term68 A s').
Proof. exact (@lem4339677 A (@EMPTY A) s'). Qed.
Lemma lem4339685 {A : Type'} (s' : A -> Prop) : (term22 A s') = (term69 A s').
Proof. exact (MK_COMB (@lem4339674 A s') (@lem4339678 A s')). Qed.
Lemma lem4339688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339689 {A : Type'} (s' : A -> Prop) : (term24 A s') = (term70 A s').
Proof. exact (MK_COMB (@lem4339688) (@lem4339685 A s')). Qed.
Lemma lem4339695 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339696 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339695 B s t). Qed.
Lemma lem4339697 {B : Type'} (t' : B -> Prop) : (@SUBSET B t' (@EMPTY B)) = (term65 B t').
Proof. exact (@lem4339696 B t' (@EMPTY B)). Qed.
Lemma lem4339704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339705 {B : Type'} (t' : B -> Prop) : (term66 B t') = (term67 B t').
Proof. exact (MK_COMB (@lem4339704) (@lem4339697 B t')). Qed.
Lemma lem4339707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339708 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339707 B s t). Qed.
Lemma lem4339709 {B : Type'} (t' : B -> Prop) : (@SUBSET B (@EMPTY B) t') = (term68 B t').
Proof. exact (@lem4339708 B (@EMPTY B) t'). Qed.
Lemma lem4339716 {B : Type'} (t' : B -> Prop) : (term22 B t') = (term69 B t').
Proof. exact (MK_COMB (@lem4339705 B t') (@lem4339709 B t')). Qed.
Lemma lem4339719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339720 {B : Type'} (t' : B -> Prop) : (term24 B t') = (term70 B t').
Proof. exact (MK_COMB (@lem4339719) (@lem4339716 B t')). Qed.
Lemma lem4339724 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339725 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339724 A s t). Qed.
Lemma lem4339726 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (@SUBSET A s' s) = (term64 A s' s).
Proof. exact (@lem4339725 A s' s). Qed.
Lemma lem4339733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339734 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term71 A s' s) = (term72 A s' s).
Proof. exact (MK_COMB (@lem4339733) (@lem4339726 A s' s)). Qed.
Lemma lem4339736 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339737 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339736 B s t). Qed.
Lemma lem4339738 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (@SUBSET B t' t) = (term64 B t' t).
Proof. exact (@lem4339737 B t' t). Qed.
Lemma lem4339745 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term25 A B s' s t' t) = (term73 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339734 A s' s) (@lem4339738 B t' t)). Qed.
Lemma lem4339748 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term27 A B s' s t' t) = (term74 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339720 B t') (@lem4339745 A B s' s t' t)). Qed.
Lemma lem4339751 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term28 A B s' s t' t) = (term75 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339689 A s') (@lem4339748 A B s' s t' t)). Qed.
Lemma lem4339754 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term31 A B s' s t' t) = (term77 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339658 A B s s' t t') (@lem4339751 A B s' s t' t)). Qed.
Lemma lem4339757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4339758 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term33 A B s' s t' t) = (term78 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339757) (@lem4339754 A B s' s t' t)). Qed.
Lemma lem4339768 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339769 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339768 A s t). Qed.
Lemma lem4339770 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@EMPTY A)) = (term65 A s).
Proof. exact (@lem4339769 A s (@EMPTY A)). Qed.
Lemma lem4339777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339778 {A : Type'} (s : A -> Prop) : (term66 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem4339777) (@lem4339770 A s)). Qed.
Lemma lem4339780 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339781 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339780 A s t). Qed.
Lemma lem4339782 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (term68 A s).
Proof. exact (@lem4339781 A (@EMPTY A) s). Qed.
Lemma lem4339789 {A : Type'} (s : A -> Prop) : (term22 A s) = (term69 A s).
Proof. exact (MK_COMB (@lem4339778 A s) (@lem4339782 A s)). Qed.
Lemma lem4339792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339793 {A : Type'} (s : A -> Prop) : (term24 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem4339792) (@lem4339789 A s)). Qed.
Lemma lem4339797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339798 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339797 B s t). Qed.
Lemma lem4339799 {B : Type'} (t : B -> Prop) : (@SUBSET B t (@EMPTY B)) = (term65 B t).
Proof. exact (@lem4339798 B t (@EMPTY B)). Qed.
Lemma lem4339806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339807 {B : Type'} (t : B -> Prop) : (term66 B t) = (term67 B t).
Proof. exact (MK_COMB (@lem4339806) (@lem4339799 B t)). Qed.
Lemma lem4339809 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339810 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339809 B s t). Qed.
Lemma lem4339811 {B : Type'} (t : B -> Prop) : (@SUBSET B (@EMPTY B) t) = (term68 B t).
Proof. exact (@lem4339810 B (@EMPTY B) t). Qed.
Lemma lem4339818 {B : Type'} (t : B -> Prop) : (term22 B t) = (term69 B t).
Proof. exact (MK_COMB (@lem4339807 B t) (@lem4339811 B t)). Qed.
Lemma lem4339821 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term35 A B s t) = (term79 A B s t).
Proof. exact (MK_COMB (@lem4339793 A s) (@lem4339818 B t)). Qed.
Lemma lem4339824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339825 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term37 A B s t) = (term80 A B s t).
Proof. exact (MK_COMB (@lem4339824) (@lem4339821 A B s t)). Qed.
Lemma lem4339831 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339832 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339831 A s t). Qed.
Lemma lem4339833 {A : Type'} (s' : A -> Prop) : (@SUBSET A s' (@EMPTY A)) = (term65 A s').
Proof. exact (@lem4339832 A s' (@EMPTY A)). Qed.
Lemma lem4339840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339841 {A : Type'} (s' : A -> Prop) : (term66 A s') = (term67 A s').
Proof. exact (MK_COMB (@lem4339840) (@lem4339833 A s')). Qed.
Lemma lem4339843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339844 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339843 A s t). Qed.
Lemma lem4339845 {A : Type'} (s' : A -> Prop) : (@SUBSET A (@EMPTY A) s') = (term68 A s').
Proof. exact (@lem4339844 A (@EMPTY A) s'). Qed.
Lemma lem4339852 {A : Type'} (s' : A -> Prop) : (term22 A s') = (term69 A s').
Proof. exact (MK_COMB (@lem4339841 A s') (@lem4339845 A s')). Qed.
Lemma lem4339855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339856 {A : Type'} (s' : A -> Prop) : (term24 A s') = (term70 A s').
Proof. exact (MK_COMB (@lem4339855) (@lem4339852 A s')). Qed.
Lemma lem4339860 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339861 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339860 B s t). Qed.
Lemma lem4339862 {B : Type'} (t' : B -> Prop) : (@SUBSET B t' (@EMPTY B)) = (term65 B t').
Proof. exact (@lem4339861 B t' (@EMPTY B)). Qed.
Lemma lem4339869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339870 {B : Type'} (t' : B -> Prop) : (term66 B t') = (term67 B t').
Proof. exact (MK_COMB (@lem4339869) (@lem4339862 B t')). Qed.
Lemma lem4339872 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339873 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339872 B s t). Qed.
Lemma lem4339874 {B : Type'} (t' : B -> Prop) : (@SUBSET B (@EMPTY B) t') = (term68 B t').
Proof. exact (@lem4339873 B (@EMPTY B) t'). Qed.
Lemma lem4339881 {B : Type'} (t' : B -> Prop) : (term22 B t') = (term69 B t').
Proof. exact (MK_COMB (@lem4339870 B t') (@lem4339874 B t')). Qed.
Lemma lem4339884 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term35 A B s' t') = (term79 A B s' t').
Proof. exact (MK_COMB (@lem4339856 A s') (@lem4339881 B t')). Qed.
Lemma lem4339887 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term39 A B s t s' t') = (term81 A B s t s' t').
Proof. exact (MK_COMB (@lem4339825 A B s t) (@lem4339884 A B s' t')). Qed.
Lemma lem4339890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4339891 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term41 A B s t s' t') = (term82 A B s t s' t').
Proof. exact (MK_COMB (@lem4339890) (@lem4339887 A B s t s' t')). Qed.
Lemma lem4339897 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339898 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339897 A s t). Qed.
Lemma lem4339899 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (@SUBSET A s s') = (term64 A s s').
Proof. exact (@lem4339898 A s s'). Qed.
Lemma lem4339906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339907 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term71 A s s') = (term72 A s s').
Proof. exact (MK_COMB (@lem4339906) (@lem4339899 A s s')). Qed.
Lemma lem4339909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (@lem4339909 A s t). Qed.
Lemma lem4339911 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (@SUBSET A s' s) = (term64 A s' s).
Proof. exact (@lem4339910 A s' s). Qed.
Lemma lem4339918 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term0 A s' s) = (term83 A s' s).
Proof. exact (MK_COMB (@lem4339907 A s s') (@lem4339911 A s' s)). Qed.
Lemma lem4339921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339922 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term43 A s' s) = (term84 A s' s).
Proof. exact (MK_COMB (@lem4339921) (@lem4339918 A s' s)). Qed.
Lemma lem4339926 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339927 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339926 B s t). Qed.
Lemma lem4339928 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (@SUBSET B t t') = (term64 B t t').
Proof. exact (@lem4339927 B t t'). Qed.
Lemma lem4339935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4339936 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term71 B t t') = (term72 B t t').
Proof. exact (MK_COMB (@lem4339935) (@lem4339928 B t t')). Qed.
Lemma lem4339938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4339939 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem4339938 B s t). Qed.
Lemma lem4339940 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (@SUBSET B t' t) = (term64 B t' t).
Proof. exact (@lem4339939 B t' t). Qed.
Lemma lem4339947 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term0 B t' t) = (term83 B t' t).
Proof. exact (MK_COMB (@lem4339936 B t t') (@lem4339940 B t' t)). Qed.
Lemma lem4339950 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term45 A B s' s t' t) = (term85 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339922 A s' s) (@lem4339947 B t' t)). Qed.
Lemma lem4339953 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term47 A B s' s t' t) = (term86 A B s' s t' t).
Proof. exact (MK_COMB (@lem4339891 A B s t s' t') (@lem4339950 A B s' s t' t)). Qed.
Lemma lem4339956 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term31 A B s' s t' t) = (term47 A B s' s t' t)) = ((term77 A B s' s t' t) = (term86 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4339758 A B s' s t' t) (@lem4339953 A B s' s t' t)). Qed.
Lemma lem4339961 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term49 A B s' s t) = (term87 A B s' s t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem4339956 A B s' s t' t)). Qed.
Lemma lem4339962 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4339963 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term51 A B s' s t) = (term88 A B s' s t).
Proof. exact (MK_COMB (@lem4339962 B) (@lem4339961 A B s' s t)). Qed.
Lemma lem4339968 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term53 A B s' s) = (term89 A B s' s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4339963 A B s' s t)). Qed.
Lemma lem4339969 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4339970 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term55 A B s' s) = (term90 A B s' s).
Proof. exact (MK_COMB (@lem4339969 B) (@lem4339968 A B s' s)). Qed.
Lemma lem4339975 {A B : Type'} (s : A -> Prop) : (term57 A B s) = (term91 A B s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem4339970 A B s' s)). Qed.
Lemma lem4339976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4339977 {A B : Type'} (s : A -> Prop) : (term59 A B s) = (term92 A B s).
Proof. exact (MK_COMB (@lem4339976 A) (@lem4339975 A B s)). Qed.
Lemma lem4339982 {A B : Type'} : (term61 A B) = (term93 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4339977 A B s)). Qed.
Lemma lem4339983 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4339984 {A B : Type'} : (term63 A B) = (term94 A B).
Proof. exact (MK_COMB (@lem4339983 A) (@lem4339982 A B)). Qed.
Lemma lem4339989 {A B : Type'} : (term94 A B) = (term63 A B).
Proof. exact (SYM (@lem4339984 A B)). Qed.
Lemma lem4340021 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340022 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340021 A P x). Qed.
Lemma lem4340023 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340022 A s x). Qed.
Lemma lem4340024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340025 {A : Type'} (s : A -> Prop) (x : A) : (term95 A x s) = (term96 A s x).
Proof. exact (MK_COMB (@lem4340024) (@lem4340023 A s x)). Qed.
Lemma lem4340027 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340028 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340027 A x). Qed.
Lemma lem4340029 {A : Type'} (s : A -> Prop) (x : A) : (term97 A s x) = (term98 A s x).
Proof. exact (MK_COMB (@lem4340025 A s x) (@lem4340028 A x)). Qed.
Lemma lem4340031 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340032 {A : Type'} (s : A -> Prop) (x : A) : (term98 A s x) = (term99 A s x).
Proof. exact (@lem4340031 (s x)). Qed.
Lemma lem4340033 {A : Type'} (s : A -> Prop) (x : A) : (term97 A s x) = (term99 A s x).
Proof. exact (TRANS (@lem4340029 A s x) (@lem4340032 A s x)). Qed.
Lemma lem4340034 {A : Type'} (s : A -> Prop) : (term100 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4340033 A s x)). Qed.
Lemma lem4340035 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340036 {A : Type'} (s : A -> Prop) : (term65 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4340035 A) (@lem4340034 A s)). Qed.
Lemma lem4340041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340042 {A : Type'} (s : A -> Prop) : (term67 A s) = (term103 A s).
Proof. exact (MK_COMB (@lem4340041) (@lem4340036 A s)). Qed.
Lemma lem4340050 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340051 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340050 A x). Qed.
Lemma lem4340052 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340053 {A : Type'} (x : A) : (term104 A x) = (imp False).
Proof. exact (MK_COMB (@lem4340052) (@lem4340051 A x)). Qed.
Lemma lem4340055 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340056 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340055 A P x). Qed.
Lemma lem4340057 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340056 A s x). Qed.
Lemma lem4340058 {A : Type'} (s : A -> Prop) (x : A) : (term105 A x s) = (term106 A s x).
Proof. exact (MK_COMB (@lem4340053 A x) (@lem4340057 A s x)). Qed.
Lemma lem4340060 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340061 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = True.
Proof. exact (@lem4340060 (s x)). Qed.
Lemma lem4340062 {A : Type'} (x : A) (s : A -> Prop) : (term105 A x s) = True.
Proof. exact (TRANS (@lem4340058 A s x) (@lem4340061 A s x)). Qed.
Lemma lem4340063 {A : Type'} (s : A -> Prop) : (term107 A s) = (term108 A).
Proof. exact (fun_ext (fun x : A => @lem4340062 A x s)). Qed.
Lemma lem4340064 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340065 {A : Type'} (s : A -> Prop) : (term68 A s) = (term109 A).
Proof. exact (MK_COMB (@lem4340064 A) (@lem4340063 A s)). Qed.
Lemma lem4340067 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340068 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (@lem4340067 A t). Qed.
Lemma lem4340069 {A : Type'} : (term109 A) = True.
Proof. exact (@lem4340068 A True). Qed.
Lemma lem4340070 {A : Type'} (s : A -> Prop) : (term68 A s) = True.
Proof. exact (TRANS (@lem4340065 A s) (@lem4340069 A)). Qed.
Lemma lem4340071 {A : Type'} (s : A -> Prop) : (term69 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem4340042 A s) (@lem4340070 A s)). Qed.
Lemma lem4340073 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340074 {A : Type'} (s : A -> Prop) : (term111 A s) = (term102 A s).
Proof. exact (@lem4340073 (term102 A s)). Qed.
Lemma lem4340079 {A : Type'} (s : A -> Prop) : (term69 A s) = (term102 A s).
Proof. exact (TRANS (@lem4340071 A s) (@lem4340074 A s)). Qed.
Lemma lem4340080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4340081 {A : Type'} (s : A -> Prop) : (term70 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4340080) (@lem4340079 A s)). Qed.
Lemma lem4340093 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340094 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340093 B P x). Qed.
Lemma lem4340095 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340094 B t x). Qed.
Lemma lem4340096 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340097 {B : Type'} (t : B -> Prop) (x : B) : (term95 B x t) = (term96 B t x).
Proof. exact (MK_COMB (@lem4340096) (@lem4340095 B t x)). Qed.
Lemma lem4340099 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340100 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340099 B x). Qed.
Lemma lem4340101 {B : Type'} (t : B -> Prop) (x : B) : (term97 B t x) = (term98 B t x).
Proof. exact (MK_COMB (@lem4340097 B t x) (@lem4340100 B x)). Qed.
Lemma lem4340103 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340104 {B : Type'} (t : B -> Prop) (x : B) : (term98 B t x) = (term99 B t x).
Proof. exact (@lem4340103 (t x)). Qed.
Lemma lem4340105 {B : Type'} (t : B -> Prop) (x : B) : (term97 B t x) = (term99 B t x).
Proof. exact (TRANS (@lem4340101 B t x) (@lem4340104 B t x)). Qed.
Lemma lem4340106 {B : Type'} (t : B -> Prop) : (term100 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4340105 B t x)). Qed.
Lemma lem4340107 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340108 {B : Type'} (t : B -> Prop) : (term65 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4340107 B) (@lem4340106 B t)). Qed.
Lemma lem4340113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340114 {B : Type'} (t : B -> Prop) : (term67 B t) = (term103 B t).
Proof. exact (MK_COMB (@lem4340113) (@lem4340108 B t)). Qed.
Lemma lem4340122 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340123 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340122 B x). Qed.
Lemma lem4340124 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340125 {B : Type'} (x : B) : (term104 B x) = (imp False).
Proof. exact (MK_COMB (@lem4340124) (@lem4340123 B x)). Qed.
Lemma lem4340127 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340128 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340127 B P x). Qed.
Lemma lem4340129 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340128 B t x). Qed.
Lemma lem4340130 {B : Type'} (t : B -> Prop) (x : B) : (term105 B x t) = (term106 B t x).
Proof. exact (MK_COMB (@lem4340125 B x) (@lem4340129 B t x)). Qed.
Lemma lem4340132 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340133 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = True.
Proof. exact (@lem4340132 (t x)). Qed.
Lemma lem4340134 {B : Type'} (x : B) (t : B -> Prop) : (term105 B x t) = True.
Proof. exact (TRANS (@lem4340130 B t x) (@lem4340133 B t x)). Qed.
Lemma lem4340135 {B : Type'} (t : B -> Prop) : (term107 B t) = (term108 B).
Proof. exact (fun_ext (fun x : B => @lem4340134 B x t)). Qed.
Lemma lem4340136 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340137 {B : Type'} (t : B -> Prop) : (term68 B t) = (term109 B).
Proof. exact (MK_COMB (@lem4340136 B) (@lem4340135 B t)). Qed.
Lemma lem4340139 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340140 {B : Type'} (t : Prop) : (term110 B t) = t.
Proof. exact (@lem4340139 B t). Qed.
Lemma lem4340141 {B : Type'} : (term109 B) = True.
Proof. exact (@lem4340140 B True). Qed.
Lemma lem4340142 {B : Type'} (t : B -> Prop) : (term68 B t) = True.
Proof. exact (TRANS (@lem4340137 B t) (@lem4340141 B)). Qed.
Lemma lem4340143 {B : Type'} (t : B -> Prop) : (term69 B t) = (term111 B t).
Proof. exact (MK_COMB (@lem4340114 B t) (@lem4340142 B t)). Qed.
Lemma lem4340145 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340146 {B : Type'} (t : B -> Prop) : (term111 B t) = (term102 B t).
Proof. exact (@lem4340145 (term102 B t)). Qed.
Lemma lem4340151 {B : Type'} (t : B -> Prop) : (term69 B t) = (term102 B t).
Proof. exact (TRANS (@lem4340143 B t) (@lem4340146 B t)). Qed.
Lemma lem4340152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4340153 {B : Type'} (t : B -> Prop) : (term70 B t) = (term112 B t).
Proof. exact (MK_COMB (@lem4340152) (@lem4340151 B t)). Qed.
Lemma lem4340163 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340164 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340163 A P x). Qed.
Lemma lem4340165 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340164 A s x). Qed.
Lemma lem4340166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340167 {A : Type'} (s : A -> Prop) (x : A) : (term95 A x s) = (term96 A s x).
Proof. exact (MK_COMB (@lem4340166) (@lem4340165 A s x)). Qed.
Lemma lem4340169 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340169 A P x). Qed.
Lemma lem4340171 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340170 A s' x). Qed.
Lemma lem4340172 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term113 A s x s') = (term114 A s s' x).
Proof. exact (MK_COMB (@lem4340167 A s x) (@lem4340171 A s' x)). Qed.
Lemma lem4340175 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term115 A s s') = (term116 A s s').
Proof. exact (fun_ext (fun x : A => @lem4340172 A s s' x)). Qed.
Lemma lem4340176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340177 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term64 A s s') = (term117 A s s').
Proof. exact (MK_COMB (@lem4340176 A) (@lem4340175 A s s')). Qed.
Lemma lem4340182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340183 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term72 A s s') = (term118 A s s').
Proof. exact (MK_COMB (@lem4340182) (@lem4340177 A s s')). Qed.
Lemma lem4340191 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340192 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340191 B P x). Qed.
Lemma lem4340193 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340192 B t x). Qed.
Lemma lem4340194 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340195 {B : Type'} (t : B -> Prop) (x : B) : (term95 B x t) = (term96 B t x).
Proof. exact (MK_COMB (@lem4340194) (@lem4340193 B t x)). Qed.
Lemma lem4340197 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340198 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340197 B P x). Qed.
Lemma lem4340199 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340198 B t' x). Qed.
Lemma lem4340200 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term113 B t x t') = (term114 B t t' x).
Proof. exact (MK_COMB (@lem4340195 B t x) (@lem4340199 B t' x)). Qed.
Lemma lem4340203 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term115 B t t') = (term116 B t t').
Proof. exact (fun_ext (fun x : B => @lem4340200 B t t' x)). Qed.
Lemma lem4340204 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340205 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term64 B t t') = (term117 B t t').
Proof. exact (MK_COMB (@lem4340204 B) (@lem4340203 B t t')). Qed.
Lemma lem4340210 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term73 A B s s' t t') = (term119 A B s s' t t').
Proof. exact (MK_COMB (@lem4340183 A s s') (@lem4340205 B t t')). Qed.
Lemma lem4340213 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term74 A B s s' t t') = (term120 A B s s' t t').
Proof. exact (MK_COMB (@lem4340153 B t) (@lem4340210 A B s s' t t')). Qed.
Lemma lem4340216 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term75 A B s s' t t') = (term121 A B s s' t t').
Proof. exact (MK_COMB (@lem4340081 A s) (@lem4340213 A B s s' t t')). Qed.
Lemma lem4340219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340220 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term76 A B s s' t t') = (term122 A B s s' t t').
Proof. exact (MK_COMB (@lem4340219) (@lem4340216 A B s s' t t')). Qed.
Lemma lem4340232 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340233 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340232 A P x). Qed.
Lemma lem4340234 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340233 A s' x). Qed.
Lemma lem4340235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340236 {A : Type'} (s' : A -> Prop) (x : A) : (term95 A x s') = (term96 A s' x).
Proof. exact (MK_COMB (@lem4340235) (@lem4340234 A s' x)). Qed.
Lemma lem4340238 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340239 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340238 A x). Qed.
Lemma lem4340240 {A : Type'} (s' : A -> Prop) (x : A) : (term97 A s' x) = (term98 A s' x).
Proof. exact (MK_COMB (@lem4340236 A s' x) (@lem4340239 A x)). Qed.
Lemma lem4340242 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340243 {A : Type'} (s' : A -> Prop) (x : A) : (term98 A s' x) = (term99 A s' x).
Proof. exact (@lem4340242 (s' x)). Qed.
Lemma lem4340244 {A : Type'} (s' : A -> Prop) (x : A) : (term97 A s' x) = (term99 A s' x).
Proof. exact (TRANS (@lem4340240 A s' x) (@lem4340243 A s' x)). Qed.
Lemma lem4340245 {A : Type'} (s' : A -> Prop) : (term100 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4340244 A s' x)). Qed.
Lemma lem4340246 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340247 {A : Type'} (s' : A -> Prop) : (term65 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4340246 A) (@lem4340245 A s')). Qed.
Lemma lem4340252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340253 {A : Type'} (s' : A -> Prop) : (term67 A s') = (term103 A s').
Proof. exact (MK_COMB (@lem4340252) (@lem4340247 A s')). Qed.
Lemma lem4340261 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340262 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340261 A x). Qed.
Lemma lem4340263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340264 {A : Type'} (x : A) : (term104 A x) = (imp False).
Proof. exact (MK_COMB (@lem4340263) (@lem4340262 A x)). Qed.
Lemma lem4340266 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340267 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340266 A P x). Qed.
Lemma lem4340268 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340267 A s' x). Qed.
Lemma lem4340269 {A : Type'} (s' : A -> Prop) (x : A) : (term105 A x s') = (term106 A s' x).
Proof. exact (MK_COMB (@lem4340264 A x) (@lem4340268 A s' x)). Qed.
Lemma lem4340271 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340272 {A : Type'} (s' : A -> Prop) (x : A) : (term106 A s' x) = True.
Proof. exact (@lem4340271 (s' x)). Qed.
Lemma lem4340273 {A : Type'} (x : A) (s' : A -> Prop) : (term105 A x s') = True.
Proof. exact (TRANS (@lem4340269 A s' x) (@lem4340272 A s' x)). Qed.
Lemma lem4340274 {A : Type'} (s' : A -> Prop) : (term107 A s') = (term108 A).
Proof. exact (fun_ext (fun x : A => @lem4340273 A x s')). Qed.
Lemma lem4340275 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340276 {A : Type'} (s' : A -> Prop) : (term68 A s') = (term109 A).
Proof. exact (MK_COMB (@lem4340275 A) (@lem4340274 A s')). Qed.
Lemma lem4340278 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340279 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (@lem4340278 A t). Qed.
Lemma lem4340280 {A : Type'} : (term109 A) = True.
Proof. exact (@lem4340279 A True). Qed.
Lemma lem4340281 {A : Type'} (s' : A -> Prop) : (term68 A s') = True.
Proof. exact (TRANS (@lem4340276 A s') (@lem4340280 A)). Qed.
Lemma lem4340282 {A : Type'} (s' : A -> Prop) : (term69 A s') = (term111 A s').
Proof. exact (MK_COMB (@lem4340253 A s') (@lem4340281 A s')). Qed.
Lemma lem4340284 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340285 {A : Type'} (s' : A -> Prop) : (term111 A s') = (term102 A s').
Proof. exact (@lem4340284 (term102 A s')). Qed.
Lemma lem4340290 {A : Type'} (s' : A -> Prop) : (term69 A s') = (term102 A s').
Proof. exact (TRANS (@lem4340282 A s') (@lem4340285 A s')). Qed.
Lemma lem4340291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4340292 {A : Type'} (s' : A -> Prop) : (term70 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4340291) (@lem4340290 A s')). Qed.
Lemma lem4340304 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340305 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340304 B P x). Qed.
Lemma lem4340306 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340305 B t' x). Qed.
Lemma lem4340307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340308 {B : Type'} (t' : B -> Prop) (x : B) : (term95 B x t') = (term96 B t' x).
Proof. exact (MK_COMB (@lem4340307) (@lem4340306 B t' x)). Qed.
Lemma lem4340310 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340311 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340310 B x). Qed.
Lemma lem4340312 {B : Type'} (t' : B -> Prop) (x : B) : (term97 B t' x) = (term98 B t' x).
Proof. exact (MK_COMB (@lem4340308 B t' x) (@lem4340311 B x)). Qed.
Lemma lem4340314 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340315 {B : Type'} (t' : B -> Prop) (x : B) : (term98 B t' x) = (term99 B t' x).
Proof. exact (@lem4340314 (t' x)). Qed.
Lemma lem4340316 {B : Type'} (t' : B -> Prop) (x : B) : (term97 B t' x) = (term99 B t' x).
Proof. exact (TRANS (@lem4340312 B t' x) (@lem4340315 B t' x)). Qed.
Lemma lem4340317 {B : Type'} (t' : B -> Prop) : (term100 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4340316 B t' x)). Qed.
Lemma lem4340318 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340319 {B : Type'} (t' : B -> Prop) : (term65 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4340318 B) (@lem4340317 B t')). Qed.
Lemma lem4340324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340325 {B : Type'} (t' : B -> Prop) : (term67 B t') = (term103 B t').
Proof. exact (MK_COMB (@lem4340324) (@lem4340319 B t')). Qed.
Lemma lem4340333 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340334 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340333 B x). Qed.
Lemma lem4340335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340336 {B : Type'} (x : B) : (term104 B x) = (imp False).
Proof. exact (MK_COMB (@lem4340335) (@lem4340334 B x)). Qed.
Lemma lem4340338 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340339 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340338 B P x). Qed.
Lemma lem4340340 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340339 B t' x). Qed.
Lemma lem4340341 {B : Type'} (t' : B -> Prop) (x : B) : (term105 B x t') = (term106 B t' x).
Proof. exact (MK_COMB (@lem4340336 B x) (@lem4340340 B t' x)). Qed.
Lemma lem4340343 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340344 {B : Type'} (t' : B -> Prop) (x : B) : (term106 B t' x) = True.
Proof. exact (@lem4340343 (t' x)). Qed.
Lemma lem4340345 {B : Type'} (x : B) (t' : B -> Prop) : (term105 B x t') = True.
Proof. exact (TRANS (@lem4340341 B t' x) (@lem4340344 B t' x)). Qed.
Lemma lem4340346 {B : Type'} (t' : B -> Prop) : (term107 B t') = (term108 B).
Proof. exact (fun_ext (fun x : B => @lem4340345 B x t')). Qed.
Lemma lem4340347 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340348 {B : Type'} (t' : B -> Prop) : (term68 B t') = (term109 B).
Proof. exact (MK_COMB (@lem4340347 B) (@lem4340346 B t')). Qed.
Lemma lem4340350 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340351 {B : Type'} (t : Prop) : (term110 B t) = t.
Proof. exact (@lem4340350 B t). Qed.
Lemma lem4340352 {B : Type'} : (term109 B) = True.
Proof. exact (@lem4340351 B True). Qed.
Lemma lem4340353 {B : Type'} (t' : B -> Prop) : (term68 B t') = True.
Proof. exact (TRANS (@lem4340348 B t') (@lem4340352 B)). Qed.
Lemma lem4340354 {B : Type'} (t' : B -> Prop) : (term69 B t') = (term111 B t').
Proof. exact (MK_COMB (@lem4340325 B t') (@lem4340353 B t')). Qed.
Lemma lem4340356 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340357 {B : Type'} (t' : B -> Prop) : (term111 B t') = (term102 B t').
Proof. exact (@lem4340356 (term102 B t')). Qed.
Lemma lem4340362 {B : Type'} (t' : B -> Prop) : (term69 B t') = (term102 B t').
Proof. exact (TRANS (@lem4340354 B t') (@lem4340357 B t')). Qed.
Lemma lem4340363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4340364 {B : Type'} (t' : B -> Prop) : (term70 B t') = (term112 B t').
Proof. exact (MK_COMB (@lem4340363) (@lem4340362 B t')). Qed.
Lemma lem4340374 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340375 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340374 A P x). Qed.
Lemma lem4340376 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340375 A s' x). Qed.
Lemma lem4340377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340378 {A : Type'} (s' : A -> Prop) (x : A) : (term95 A x s') = (term96 A s' x).
Proof. exact (MK_COMB (@lem4340377) (@lem4340376 A s' x)). Qed.
Lemma lem4340380 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340381 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340380 A P x). Qed.
Lemma lem4340382 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340381 A s x). Qed.
Lemma lem4340383 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term113 A s' x s) = (term114 A s' s x).
Proof. exact (MK_COMB (@lem4340378 A s' x) (@lem4340382 A s x)). Qed.
Lemma lem4340386 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term115 A s' s) = (term116 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4340383 A s' s x)). Qed.
Lemma lem4340387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340388 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term64 A s' s) = (term117 A s' s).
Proof. exact (MK_COMB (@lem4340387 A) (@lem4340386 A s' s)). Qed.
Lemma lem4340393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340394 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term72 A s' s) = (term118 A s' s).
Proof. exact (MK_COMB (@lem4340393) (@lem4340388 A s' s)). Qed.
Lemma lem4340402 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340403 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340402 B P x). Qed.
Lemma lem4340404 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340403 B t' x). Qed.
Lemma lem4340405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340406 {B : Type'} (t' : B -> Prop) (x : B) : (term95 B x t') = (term96 B t' x).
Proof. exact (MK_COMB (@lem4340405) (@lem4340404 B t' x)). Qed.
Lemma lem4340408 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340409 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340408 B P x). Qed.
Lemma lem4340410 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340409 B t x). Qed.
Lemma lem4340411 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term113 B t' x t) = (term114 B t' t x).
Proof. exact (MK_COMB (@lem4340406 B t' x) (@lem4340410 B t x)). Qed.
Lemma lem4340414 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term115 B t' t) = (term116 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4340411 B t' t x)). Qed.
Lemma lem4340415 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340416 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term64 B t' t) = (term117 B t' t).
Proof. exact (MK_COMB (@lem4340415 B) (@lem4340414 B t' t)). Qed.
Lemma lem4340421 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term73 A B s' s t' t) = (term119 A B s' s t' t).
Proof. exact (MK_COMB (@lem4340394 A s' s) (@lem4340416 B t' t)). Qed.
Lemma lem4340424 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term74 A B s' s t' t) = (term120 A B s' s t' t).
Proof. exact (MK_COMB (@lem4340364 B t') (@lem4340421 A B s' s t' t)). Qed.
Lemma lem4340427 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term75 A B s' s t' t) = (term121 A B s' s t' t).
Proof. exact (MK_COMB (@lem4340292 A s') (@lem4340424 A B s' s t' t)). Qed.
Lemma lem4340430 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term77 A B s' s t' t) = (term123 A B s' s t' t).
Proof. exact (MK_COMB (@lem4340220 A B s s' t t') (@lem4340427 A B s' s t' t)). Qed.
Lemma lem4340433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4340434 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term78 A B s' s t' t) = (term124 A B s' s t' t).
Proof. exact (MK_COMB (@lem4340433) (@lem4340430 A B s' s t' t)). Qed.
Lemma lem4340450 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340451 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340450 A P x). Qed.
Lemma lem4340452 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340451 A s x). Qed.
Lemma lem4340453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340454 {A : Type'} (s : A -> Prop) (x : A) : (term95 A x s) = (term96 A s x).
Proof. exact (MK_COMB (@lem4340453) (@lem4340452 A s x)). Qed.
Lemma lem4340456 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340457 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340456 A x). Qed.
Lemma lem4340458 {A : Type'} (s : A -> Prop) (x : A) : (term97 A s x) = (term98 A s x).
Proof. exact (MK_COMB (@lem4340454 A s x) (@lem4340457 A x)). Qed.
Lemma lem4340460 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340461 {A : Type'} (s : A -> Prop) (x : A) : (term98 A s x) = (term99 A s x).
Proof. exact (@lem4340460 (s x)). Qed.
Lemma lem4340462 {A : Type'} (s : A -> Prop) (x : A) : (term97 A s x) = (term99 A s x).
Proof. exact (TRANS (@lem4340458 A s x) (@lem4340461 A s x)). Qed.
Lemma lem4340463 {A : Type'} (s : A -> Prop) : (term100 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4340462 A s x)). Qed.
Lemma lem4340464 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340465 {A : Type'} (s : A -> Prop) : (term65 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4340464 A) (@lem4340463 A s)). Qed.
Lemma lem4340470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340471 {A : Type'} (s : A -> Prop) : (term67 A s) = (term103 A s).
Proof. exact (MK_COMB (@lem4340470) (@lem4340465 A s)). Qed.
Lemma lem4340479 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340480 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340479 A x). Qed.
Lemma lem4340481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340482 {A : Type'} (x : A) : (term104 A x) = (imp False).
Proof. exact (MK_COMB (@lem4340481) (@lem4340480 A x)). Qed.
Lemma lem4340484 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340485 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340484 A P x). Qed.
Lemma lem4340486 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340485 A s x). Qed.
Lemma lem4340487 {A : Type'} (s : A -> Prop) (x : A) : (term105 A x s) = (term106 A s x).
Proof. exact (MK_COMB (@lem4340482 A x) (@lem4340486 A s x)). Qed.
Lemma lem4340489 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340490 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = True.
Proof. exact (@lem4340489 (s x)). Qed.
Lemma lem4340491 {A : Type'} (x : A) (s : A -> Prop) : (term105 A x s) = True.
Proof. exact (TRANS (@lem4340487 A s x) (@lem4340490 A s x)). Qed.
Lemma lem4340492 {A : Type'} (s : A -> Prop) : (term107 A s) = (term108 A).
Proof. exact (fun_ext (fun x : A => @lem4340491 A x s)). Qed.
Lemma lem4340493 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340494 {A : Type'} (s : A -> Prop) : (term68 A s) = (term109 A).
Proof. exact (MK_COMB (@lem4340493 A) (@lem4340492 A s)). Qed.
Lemma lem4340496 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340497 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (@lem4340496 A t). Qed.
Lemma lem4340498 {A : Type'} : (term109 A) = True.
Proof. exact (@lem4340497 A True). Qed.
Lemma lem4340499 {A : Type'} (s : A -> Prop) : (term68 A s) = True.
Proof. exact (TRANS (@lem4340494 A s) (@lem4340498 A)). Qed.
Lemma lem4340500 {A : Type'} (s : A -> Prop) : (term69 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem4340471 A s) (@lem4340499 A s)). Qed.
Lemma lem4340502 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340503 {A : Type'} (s : A -> Prop) : (term111 A s) = (term102 A s).
Proof. exact (@lem4340502 (term102 A s)). Qed.
Lemma lem4340508 {A : Type'} (s : A -> Prop) : (term69 A s) = (term102 A s).
Proof. exact (TRANS (@lem4340500 A s) (@lem4340503 A s)). Qed.
Lemma lem4340509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4340510 {A : Type'} (s : A -> Prop) : (term70 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4340509) (@lem4340508 A s)). Qed.
Lemma lem4340520 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340521 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340520 B P x). Qed.
Lemma lem4340522 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340521 B t x). Qed.
Lemma lem4340523 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340524 {B : Type'} (t : B -> Prop) (x : B) : (term95 B x t) = (term96 B t x).
Proof. exact (MK_COMB (@lem4340523) (@lem4340522 B t x)). Qed.
Lemma lem4340526 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340527 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340526 B x). Qed.
Lemma lem4340528 {B : Type'} (t : B -> Prop) (x : B) : (term97 B t x) = (term98 B t x).
Proof. exact (MK_COMB (@lem4340524 B t x) (@lem4340527 B x)). Qed.
Lemma lem4340530 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340531 {B : Type'} (t : B -> Prop) (x : B) : (term98 B t x) = (term99 B t x).
Proof. exact (@lem4340530 (t x)). Qed.
Lemma lem4340532 {B : Type'} (t : B -> Prop) (x : B) : (term97 B t x) = (term99 B t x).
Proof. exact (TRANS (@lem4340528 B t x) (@lem4340531 B t x)). Qed.
Lemma lem4340533 {B : Type'} (t : B -> Prop) : (term100 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4340532 B t x)). Qed.
Lemma lem4340534 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340535 {B : Type'} (t : B -> Prop) : (term65 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4340534 B) (@lem4340533 B t)). Qed.
Lemma lem4340540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340541 {B : Type'} (t : B -> Prop) : (term67 B t) = (term103 B t).
Proof. exact (MK_COMB (@lem4340540) (@lem4340535 B t)). Qed.
Lemma lem4340549 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340550 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340549 B x). Qed.
Lemma lem4340551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340552 {B : Type'} (x : B) : (term104 B x) = (imp False).
Proof. exact (MK_COMB (@lem4340551) (@lem4340550 B x)). Qed.
Lemma lem4340554 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340555 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340554 B P x). Qed.
Lemma lem4340556 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340555 B t x). Qed.
Lemma lem4340557 {B : Type'} (t : B -> Prop) (x : B) : (term105 B x t) = (term106 B t x).
Proof. exact (MK_COMB (@lem4340552 B x) (@lem4340556 B t x)). Qed.
Lemma lem4340559 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340560 {B : Type'} (t : B -> Prop) (x : B) : (term106 B t x) = True.
Proof. exact (@lem4340559 (t x)). Qed.
Lemma lem4340561 {B : Type'} (x : B) (t : B -> Prop) : (term105 B x t) = True.
Proof. exact (TRANS (@lem4340557 B t x) (@lem4340560 B t x)). Qed.
Lemma lem4340562 {B : Type'} (t : B -> Prop) : (term107 B t) = (term108 B).
Proof. exact (fun_ext (fun x : B => @lem4340561 B x t)). Qed.
Lemma lem4340563 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340564 {B : Type'} (t : B -> Prop) : (term68 B t) = (term109 B).
Proof. exact (MK_COMB (@lem4340563 B) (@lem4340562 B t)). Qed.
Lemma lem4340566 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340567 {B : Type'} (t : Prop) : (term110 B t) = t.
Proof. exact (@lem4340566 B t). Qed.
Lemma lem4340568 {B : Type'} : (term109 B) = True.
Proof. exact (@lem4340567 B True). Qed.
Lemma lem4340569 {B : Type'} (t : B -> Prop) : (term68 B t) = True.
Proof. exact (TRANS (@lem4340564 B t) (@lem4340568 B)). Qed.
Lemma lem4340570 {B : Type'} (t : B -> Prop) : (term69 B t) = (term111 B t).
Proof. exact (MK_COMB (@lem4340541 B t) (@lem4340569 B t)). Qed.
Lemma lem4340572 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340573 {B : Type'} (t : B -> Prop) : (term111 B t) = (term102 B t).
Proof. exact (@lem4340572 (term102 B t)). Qed.
Lemma lem4340578 {B : Type'} (t : B -> Prop) : (term69 B t) = (term102 B t).
Proof. exact (TRANS (@lem4340570 B t) (@lem4340573 B t)). Qed.
Lemma lem4340579 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term79 A B s t) = (term125 A B s t).
Proof. exact (MK_COMB (@lem4340510 A s) (@lem4340578 B t)). Qed.
Lemma lem4340582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340583 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term80 A B s t) = (term126 A B s t).
Proof. exact (MK_COMB (@lem4340582) (@lem4340579 A B s t)). Qed.
Lemma lem4340595 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340596 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340595 A P x). Qed.
Lemma lem4340597 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340596 A s' x). Qed.
Lemma lem4340598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340599 {A : Type'} (s' : A -> Prop) (x : A) : (term95 A x s') = (term96 A s' x).
Proof. exact (MK_COMB (@lem4340598) (@lem4340597 A s' x)). Qed.
Lemma lem4340601 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340602 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340601 A x). Qed.
Lemma lem4340603 {A : Type'} (s' : A -> Prop) (x : A) : (term97 A s' x) = (term98 A s' x).
Proof. exact (MK_COMB (@lem4340599 A s' x) (@lem4340602 A x)). Qed.
Lemma lem4340605 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340606 {A : Type'} (s' : A -> Prop) (x : A) : (term98 A s' x) = (term99 A s' x).
Proof. exact (@lem4340605 (s' x)). Qed.
Lemma lem4340607 {A : Type'} (s' : A -> Prop) (x : A) : (term97 A s' x) = (term99 A s' x).
Proof. exact (TRANS (@lem4340603 A s' x) (@lem4340606 A s' x)). Qed.
Lemma lem4340608 {A : Type'} (s' : A -> Prop) : (term100 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4340607 A s' x)). Qed.
Lemma lem4340609 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340610 {A : Type'} (s' : A -> Prop) : (term65 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4340609 A) (@lem4340608 A s')). Qed.
Lemma lem4340615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340616 {A : Type'} (s' : A -> Prop) : (term67 A s') = (term103 A s').
Proof. exact (MK_COMB (@lem4340615) (@lem4340610 A s')). Qed.
Lemma lem4340624 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340625 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4340624 A x). Qed.
Lemma lem4340626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340627 {A : Type'} (x : A) : (term104 A x) = (imp False).
Proof. exact (MK_COMB (@lem4340626) (@lem4340625 A x)). Qed.
Lemma lem4340629 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340630 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340629 A P x). Qed.
Lemma lem4340631 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340630 A s' x). Qed.
Lemma lem4340632 {A : Type'} (s' : A -> Prop) (x : A) : (term105 A x s') = (term106 A s' x).
Proof. exact (MK_COMB (@lem4340627 A x) (@lem4340631 A s' x)). Qed.
Lemma lem4340634 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340635 {A : Type'} (s' : A -> Prop) (x : A) : (term106 A s' x) = True.
Proof. exact (@lem4340634 (s' x)). Qed.
Lemma lem4340636 {A : Type'} (x : A) (s' : A -> Prop) : (term105 A x s') = True.
Proof. exact (TRANS (@lem4340632 A s' x) (@lem4340635 A s' x)). Qed.
Lemma lem4340637 {A : Type'} (s' : A -> Prop) : (term107 A s') = (term108 A).
Proof. exact (fun_ext (fun x : A => @lem4340636 A x s')). Qed.
Lemma lem4340638 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340639 {A : Type'} (s' : A -> Prop) : (term68 A s') = (term109 A).
Proof. exact (MK_COMB (@lem4340638 A) (@lem4340637 A s')). Qed.
Lemma lem4340641 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340642 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (@lem4340641 A t). Qed.
Lemma lem4340643 {A : Type'} : (term109 A) = True.
Proof. exact (@lem4340642 A True). Qed.
Lemma lem4340644 {A : Type'} (s' : A -> Prop) : (term68 A s') = True.
Proof. exact (TRANS (@lem4340639 A s') (@lem4340643 A)). Qed.
Lemma lem4340645 {A : Type'} (s' : A -> Prop) : (term69 A s') = (term111 A s').
Proof. exact (MK_COMB (@lem4340616 A s') (@lem4340644 A s')). Qed.
Lemma lem4340647 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340648 {A : Type'} (s' : A -> Prop) : (term111 A s') = (term102 A s').
Proof. exact (@lem4340647 (term102 A s')). Qed.
Lemma lem4340653 {A : Type'} (s' : A -> Prop) : (term69 A s') = (term102 A s').
Proof. exact (TRANS (@lem4340645 A s') (@lem4340648 A s')). Qed.
Lemma lem4340654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4340655 {A : Type'} (s' : A -> Prop) : (term70 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4340654) (@lem4340653 A s')). Qed.
Lemma lem4340665 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340666 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340665 B P x). Qed.
Lemma lem4340667 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340666 B t' x). Qed.
Lemma lem4340668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340669 {B : Type'} (t' : B -> Prop) (x : B) : (term95 B x t') = (term96 B t' x).
Proof. exact (MK_COMB (@lem4340668) (@lem4340667 B t' x)). Qed.
Lemma lem4340671 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340672 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340671 B x). Qed.
Lemma lem4340673 {B : Type'} (t' : B -> Prop) (x : B) : (term97 B t' x) = (term98 B t' x).
Proof. exact (MK_COMB (@lem4340669 B t' x) (@lem4340672 B x)). Qed.
Lemma lem4340675 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4340676 {B : Type'} (t' : B -> Prop) (x : B) : (term98 B t' x) = (term99 B t' x).
Proof. exact (@lem4340675 (t' x)). Qed.
Lemma lem4340677 {B : Type'} (t' : B -> Prop) (x : B) : (term97 B t' x) = (term99 B t' x).
Proof. exact (TRANS (@lem4340673 B t' x) (@lem4340676 B t' x)). Qed.
Lemma lem4340678 {B : Type'} (t' : B -> Prop) : (term100 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4340677 B t' x)). Qed.
Lemma lem4340679 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340680 {B : Type'} (t' : B -> Prop) : (term65 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4340679 B) (@lem4340678 B t')). Qed.
Lemma lem4340685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340686 {B : Type'} (t' : B -> Prop) : (term67 B t') = (term103 B t').
Proof. exact (MK_COMB (@lem4340685) (@lem4340680 B t')). Qed.
Lemma lem4340694 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4340695 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem4340694 B x). Qed.
Lemma lem4340696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340697 {B : Type'} (x : B) : (term104 B x) = (imp False).
Proof. exact (MK_COMB (@lem4340696) (@lem4340695 B x)). Qed.
Lemma lem4340699 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340700 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340699 B P x). Qed.
Lemma lem4340701 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340700 B t' x). Qed.
Lemma lem4340702 {B : Type'} (t' : B -> Prop) (x : B) : (term105 B x t') = (term106 B t' x).
Proof. exact (MK_COMB (@lem4340697 B x) (@lem4340701 B t' x)). Qed.
Lemma lem4340704 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4340705 {B : Type'} (t' : B -> Prop) (x : B) : (term106 B t' x) = True.
Proof. exact (@lem4340704 (t' x)). Qed.
Lemma lem4340706 {B : Type'} (x : B) (t' : B -> Prop) : (term105 B x t') = True.
Proof. exact (TRANS (@lem4340702 B t' x) (@lem4340705 B t' x)). Qed.
Lemma lem4340707 {B : Type'} (t' : B -> Prop) : (term107 B t') = (term108 B).
Proof. exact (fun_ext (fun x : B => @lem4340706 B x t')). Qed.
Lemma lem4340708 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340709 {B : Type'} (t' : B -> Prop) : (term68 B t') = (term109 B).
Proof. exact (MK_COMB (@lem4340708 B) (@lem4340707 B t')). Qed.
Lemma lem4340711 {A : Type'} (t : Prop) : (term110 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4340712 {B : Type'} (t : Prop) : (term110 B t) = t.
Proof. exact (@lem4340711 B t). Qed.
Lemma lem4340713 {B : Type'} : (term109 B) = True.
Proof. exact (@lem4340712 B True). Qed.
Lemma lem4340714 {B : Type'} (t' : B -> Prop) : (term68 B t') = True.
Proof. exact (TRANS (@lem4340709 B t') (@lem4340713 B)). Qed.
Lemma lem4340715 {B : Type'} (t' : B -> Prop) : (term69 B t') = (term111 B t').
Proof. exact (MK_COMB (@lem4340686 B t') (@lem4340714 B t')). Qed.
Lemma lem4340717 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4340718 {B : Type'} (t' : B -> Prop) : (term111 B t') = (term102 B t').
Proof. exact (@lem4340717 (term102 B t')). Qed.
Lemma lem4340723 {B : Type'} (t' : B -> Prop) : (term69 B t') = (term102 B t').
Proof. exact (TRANS (@lem4340715 B t') (@lem4340718 B t')). Qed.
Lemma lem4340724 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term79 A B s' t') = (term125 A B s' t').
Proof. exact (MK_COMB (@lem4340655 A s') (@lem4340723 B t')). Qed.
Lemma lem4340727 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term81 A B s t s' t') = (term127 A B s t s' t').
Proof. exact (MK_COMB (@lem4340583 A B s t) (@lem4340724 A B s' t')). Qed.
Lemma lem4340730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4340731 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term82 A B s t s' t') = (term128 A B s t s' t').
Proof. exact (MK_COMB (@lem4340730) (@lem4340727 A B s t s' t')). Qed.
Lemma lem4340743 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340744 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340743 A P x). Qed.
Lemma lem4340745 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340744 A s x). Qed.
Lemma lem4340746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340747 {A : Type'} (s : A -> Prop) (x : A) : (term95 A x s) = (term96 A s x).
Proof. exact (MK_COMB (@lem4340746) (@lem4340745 A s x)). Qed.
Lemma lem4340749 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340750 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340749 A P x). Qed.
Lemma lem4340751 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340750 A s' x). Qed.
Lemma lem4340752 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term113 A s x s') = (term114 A s s' x).
Proof. exact (MK_COMB (@lem4340747 A s x) (@lem4340751 A s' x)). Qed.
Lemma lem4340755 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term115 A s s') = (term116 A s s').
Proof. exact (fun_ext (fun x : A => @lem4340752 A s s' x)). Qed.
Lemma lem4340756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340757 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term64 A s s') = (term117 A s s').
Proof. exact (MK_COMB (@lem4340756 A) (@lem4340755 A s s')). Qed.
Lemma lem4340762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340763 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term72 A s s') = (term118 A s s').
Proof. exact (MK_COMB (@lem4340762) (@lem4340757 A s s')). Qed.
Lemma lem4340771 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340772 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340771 A P x). Qed.
Lemma lem4340773 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem4340772 A s' x). Qed.
Lemma lem4340774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340775 {A : Type'} (s' : A -> Prop) (x : A) : (term95 A x s') = (term96 A s' x).
Proof. exact (MK_COMB (@lem4340774) (@lem4340773 A s' x)). Qed.
Lemma lem4340777 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340778 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4340777 A P x). Qed.
Lemma lem4340779 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4340778 A s x). Qed.
Lemma lem4340780 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term113 A s' x s) = (term114 A s' s x).
Proof. exact (MK_COMB (@lem4340775 A s' x) (@lem4340779 A s x)). Qed.
Lemma lem4340783 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term115 A s' s) = (term116 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4340780 A s' s x)). Qed.
Lemma lem4340784 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4340785 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term64 A s' s) = (term117 A s' s).
Proof. exact (MK_COMB (@lem4340784 A) (@lem4340783 A s' s)). Qed.
Lemma lem4340790 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term83 A s' s) = (term129 A s' s).
Proof. exact (MK_COMB (@lem4340763 A s s') (@lem4340785 A s' s)). Qed.
Lemma lem4340793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340794 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term84 A s' s) = (term130 A s' s).
Proof. exact (MK_COMB (@lem4340793) (@lem4340790 A s' s)). Qed.
Lemma lem4340804 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340805 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340804 B P x). Qed.
Lemma lem4340806 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340805 B t x). Qed.
Lemma lem4340807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340808 {B : Type'} (t : B -> Prop) (x : B) : (term95 B x t) = (term96 B t x).
Proof. exact (MK_COMB (@lem4340807) (@lem4340806 B t x)). Qed.
Lemma lem4340810 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340811 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340810 B P x). Qed.
Lemma lem4340812 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340811 B t' x). Qed.
Lemma lem4340813 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term113 B t x t') = (term114 B t t' x).
Proof. exact (MK_COMB (@lem4340808 B t x) (@lem4340812 B t' x)). Qed.
Lemma lem4340816 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term115 B t t') = (term116 B t t').
Proof. exact (fun_ext (fun x : B => @lem4340813 B t t' x)). Qed.
Lemma lem4340817 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340818 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term64 B t t') = (term117 B t t').
Proof. exact (MK_COMB (@lem4340817 B) (@lem4340816 B t t')). Qed.
Lemma lem4340823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4340824 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term72 B t t') = (term118 B t t').
Proof. exact (MK_COMB (@lem4340823) (@lem4340818 B t t')). Qed.
Lemma lem4340832 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340833 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340832 B P x). Qed.
Lemma lem4340834 {B : Type'} (t' : B -> Prop) (x : B) : (@IN B x t') = (t' x).
Proof. exact (@lem4340833 B t' x). Qed.
Lemma lem4340835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4340836 {B : Type'} (t' : B -> Prop) (x : B) : (term95 B x t') = (term96 B t' x).
Proof. exact (MK_COMB (@lem4340835) (@lem4340834 B t' x)). Qed.
Lemma lem4340838 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4340839 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem4340838 B P x). Qed.
Lemma lem4340840 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem4340839 B t x). Qed.
Lemma lem4340841 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term113 B t' x t) = (term114 B t' t x).
Proof. exact (MK_COMB (@lem4340836 B t' x) (@lem4340840 B t x)). Qed.
Lemma lem4340844 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term115 B t' t) = (term116 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4340841 B t' t x)). Qed.
Lemma lem4340845 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4340846 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term64 B t' t) = (term117 B t' t).
Proof. exact (MK_COMB (@lem4340845 B) (@lem4340844 B t' t)). Qed.
Lemma lem4340851 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term83 B t' t) = (term129 B t' t).
Proof. exact (MK_COMB (@lem4340824 B t t') (@lem4340846 B t' t)). Qed.
Lemma lem4340854 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term85 A B s' s t' t) = (term131 A B s' s t' t).
Proof. exact (MK_COMB (@lem4340794 A s' s) (@lem4340851 B t' t)). Qed.
Lemma lem4340857 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term86 A B s' s t' t) = (term132 A B s' s t' t).
Proof. exact (MK_COMB (@lem4340731 A B s t s' t') (@lem4340854 A B s' s t' t)). Qed.
Lemma lem4340860 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term77 A B s' s t' t) = (term86 A B s' s t' t)) = ((term123 A B s' s t' t) = (term132 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4340434 A B s' s t' t) (@lem4340857 A B s' s t' t)). Qed.
Lemma lem4340863 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term87 A B s' s t) = (term133 A B s' s t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem4340860 A B s' s t' t)). Qed.
Lemma lem4340864 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4340865 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term88 A B s' s t) = (term134 A B s' s t).
Proof. exact (MK_COMB (@lem4340864 B) (@lem4340863 A B s' s t)). Qed.
Lemma lem4340870 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term89 A B s' s) = (term135 A B s' s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4340865 A B s' s t)). Qed.
Lemma lem4340871 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4340872 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term90 A B s' s) = (term136 A B s' s).
Proof. exact (MK_COMB (@lem4340871 B) (@lem4340870 A B s' s)). Qed.
Lemma lem4340877 {A B : Type'} (s : A -> Prop) : (term91 A B s) = (term137 A B s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem4340872 A B s' s)). Qed.
Lemma lem4340878 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4340879 {A B : Type'} (s : A -> Prop) : (term92 A B s) = (term138 A B s).
Proof. exact (MK_COMB (@lem4340878 A) (@lem4340877 A B s)). Qed.
Lemma lem4340884 {A B : Type'} : (term93 A B) = (term139 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4340879 A B s)). Qed.
Lemma lem4340885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4340886 {A B : Type'} : (term94 A B) = (term140 A B).
Proof. exact (MK_COMB (@lem4340885 A) (@lem4340884 A B)). Qed.
Lemma lem4340891 {A B : Type'} : (term140 A B) = (term94 A B).
Proof. exact (SYM (@lem4340886 A B)). Qed.
Lemma lem4340893 (p : Prop) : p = (term141 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4340894 {A B : Type'} : (term140 A B) = (term142 A B).
Proof. exact (@lem4340893 (term140 A B)). Qed.
Lemma lem4340895 {A B : Type'} : (term142 A B) = (term140 A B).
Proof. exact (SYM (@lem4340894 A B)). Qed.
Lemma lem4340896 {A B : Type'} (h1 : term143 A B) : term143 A B.
Proof. exact (h1). Qed.
Lemma lem4340899 {A B : Type'} (h1 : term142 A B) : term142 A B.
Proof. exact (h1). Qed.
Lemma lem4340900 {A B : Type'} : term144 A B.
Proof. exact (fun h0 : term142 A B => @lem4340899 A B h0). Qed.
Lemma lem4340901 {A B : Type'} (h1 : term144 A B) : term144 A B.
Proof. exact (h1). Qed.
Lemma lem4340902 {A B : Type'} (h1 : term142 A B) : term142 A B.
Proof. exact (h1). Qed.
Lemma lem4340903 {A B : Type'} (h1 : term142 A B) (h2 : term144 A B) : term142 A B.
Proof. exact (@lem4340901 A B h2 (@lem4340902 A B h1)). Qed.
Lemma lem4340904 {A B : Type'} (h1 : term142 A B) : term145 A B.
Proof. exact (fun h0 : term144 A B => @lem4340903 A B h1 h0). Qed.
Lemma lem4340905 {A B : Type'} (h1 : term144 A B) : term144 A B.
Proof. exact (h1). Qed.
Lemma lem4340906 {A B : Type'} (h1 : term142 A B) (h2 : term144 A B) : term142 A B.
Proof. exact (@lem4340904 A B h1 (@lem4340905 A B h2)). Qed.
Lemma lem4340907 {A B : Type'} (h1 : term144 A B) : term144 A B.
Proof. exact (fun h0 : term142 A B => @lem4340906 A B h0 h1). Qed.
Lemma lem4340908 {A B : Type'} : term146 A B.
Proof. exact (fun h0 : term144 A B => @lem4340907 A B h0). Qed.
Lemma lem4340911 {A B : Type'} : term144 A B.
Proof. exact (@lem4340908 A B (@lem4340900 A B)). Qed.
Lemma lem4340912 {A B : Type'} : term144 A B.
Proof. exact (@lem4340911 A B). Qed.
Lemma lem4340914 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4340915 {A B : Type'} : (term142 A B) = (term147 A B).
Proof. exact (@lem4340914 (term143 A B)). Qed.
Lemma lem4340917 (t : Prop) : (term148 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4340918 {A B : Type'} : (term147 A B) = (term140 A B).
Proof. exact (@lem4340917 (term140 A B)). Qed.
Lemma lem4341047 {A B : Type'} : (term142 A B) = (term140 A B).
Proof. exact (TRANS (@lem4340915 A B) (@lem4340918 A B)). Qed.
Lemma lem4341052 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term114 B t' t x) = (term114 B t' t x).
Proof. exact (eq_refl (term114 B t' t x)). Qed.
Lemma lem4341053 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term116 B t' t) = (term116 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4341052 B t' t x)). Qed.
Lemma lem4341054 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341055 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term117 B t' t) = (term117 B t' t).
Proof. exact (MK_COMB (@lem4341054 B) (@lem4341053 B t' t)). Qed.
Lemma lem4341060 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term114 B t t' x) = (term114 B t t' x).
Proof. exact (eq_refl (term114 B t t' x)). Qed.
Lemma lem4341061 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term116 B t t') = (term116 B t t').
Proof. exact (fun_ext (fun x : B => @lem4341060 B t t' x)). Qed.
Lemma lem4341062 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341063 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term117 B t t') = (term117 B t t').
Proof. exact (MK_COMB (@lem4341062 B) (@lem4341061 B t t')). Qed.
Lemma lem4341064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341065 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term118 B t t') = (term118 B t t').
Proof. exact (MK_COMB (@lem4341064) (@lem4341063 B t t')). Qed.
Lemma lem4341066 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term129 B t' t) = (term129 B t' t).
Proof. exact (MK_COMB (@lem4341065 B t t') (@lem4341055 B t' t)). Qed.
Lemma lem4341071 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term114 A s' s x) = (term114 A s' s x).
Proof. exact (eq_refl (term114 A s' s x)). Qed.
Lemma lem4341072 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term116 A s' s) = (term116 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4341071 A s' s x)). Qed.
Lemma lem4341073 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341074 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term117 A s' s) = (term117 A s' s).
Proof. exact (MK_COMB (@lem4341073 A) (@lem4341072 A s' s)). Qed.
Lemma lem4341079 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term114 A s s' x) = (term114 A s s' x).
Proof. exact (eq_refl (term114 A s s' x)). Qed.
Lemma lem4341080 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term116 A s s') = (term116 A s s').
Proof. exact (fun_ext (fun x : A => @lem4341079 A s s' x)). Qed.
Lemma lem4341081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341082 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term117 A s s') = (term117 A s s').
Proof. exact (MK_COMB (@lem4341081 A) (@lem4341080 A s s')). Qed.
Lemma lem4341083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341084 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term118 A s s') = (term118 A s s').
Proof. exact (MK_COMB (@lem4341083) (@lem4341082 A s s')). Qed.
Lemma lem4341085 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term129 A s' s) = (term129 A s' s).
Proof. exact (MK_COMB (@lem4341084 A s s') (@lem4341074 A s' s)). Qed.
Lemma lem4341086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341087 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term130 A s' s) = (term130 A s' s).
Proof. exact (MK_COMB (@lem4341086) (@lem4341085 A s' s)). Qed.
Lemma lem4341088 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term131 A B s' s t' t) = (term131 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341087 A s' s) (@lem4341066 B t' t)). Qed.
Lemma lem4341091 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4341092 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4341091 B t' x)). Qed.
Lemma lem4341093 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341094 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4341093 B) (@lem4341092 B t')). Qed.
Lemma lem4341097 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4341098 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4341097 A s' x)). Qed.
Lemma lem4341099 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341100 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4341099 A) (@lem4341098 A s')). Qed.
Lemma lem4341101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341102 {A : Type'} (s' : A -> Prop) : (term112 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4341101) (@lem4341100 A s')). Qed.
Lemma lem4341103 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term125 A B s' t') = (term125 A B s' t').
Proof. exact (MK_COMB (@lem4341102 A s') (@lem4341094 B t')). Qed.
Lemma lem4341106 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4341107 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4341106 B t x)). Qed.
Lemma lem4341108 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341109 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4341108 B) (@lem4341107 B t)). Qed.
Lemma lem4341112 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4341113 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4341112 A s x)). Qed.
Lemma lem4341114 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341115 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4341114 A) (@lem4341113 A s)). Qed.
Lemma lem4341116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341117 {A : Type'} (s : A -> Prop) : (term112 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4341116) (@lem4341115 A s)). Qed.
Lemma lem4341118 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term125 A B s t) = (term125 A B s t).
Proof. exact (MK_COMB (@lem4341117 A s) (@lem4341109 B t)). Qed.
Lemma lem4341119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341120 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term126 A B s t) = (term126 A B s t).
Proof. exact (MK_COMB (@lem4341119) (@lem4341118 A B s t)). Qed.
Lemma lem4341121 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term127 A B s t s' t') = (term127 A B s t s' t').
Proof. exact (MK_COMB (@lem4341120 A B s t) (@lem4341103 A B s' t')). Qed.
Lemma lem4341122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341123 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term128 A B s t s' t') = (term128 A B s t s' t').
Proof. exact (MK_COMB (@lem4341122) (@lem4341121 A B s t s' t')). Qed.
Lemma lem4341124 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term132 A B s' s t' t) = (term132 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341123 A B s t s' t') (@lem4341088 A B s' s t' t)). Qed.
Lemma lem4341129 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term114 B t' t x) = (term114 B t' t x).
Proof. exact (eq_refl (term114 B t' t x)). Qed.
Lemma lem4341130 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term116 B t' t) = (term116 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4341129 B t' t x)). Qed.
Lemma lem4341131 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341132 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term117 B t' t) = (term117 B t' t).
Proof. exact (MK_COMB (@lem4341131 B) (@lem4341130 B t' t)). Qed.
Lemma lem4341137 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term114 A s' s x) = (term114 A s' s x).
Proof. exact (eq_refl (term114 A s' s x)). Qed.
Lemma lem4341138 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term116 A s' s) = (term116 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4341137 A s' s x)). Qed.
Lemma lem4341139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341140 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term117 A s' s) = (term117 A s' s).
Proof. exact (MK_COMB (@lem4341139 A) (@lem4341138 A s' s)). Qed.
Lemma lem4341141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341142 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term118 A s' s) = (term118 A s' s).
Proof. exact (MK_COMB (@lem4341141) (@lem4341140 A s' s)). Qed.
Lemma lem4341143 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term119 A B s' s t' t) = (term119 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341142 A s' s) (@lem4341132 B t' t)). Qed.
Lemma lem4341146 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4341147 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4341146 B t' x)). Qed.
Lemma lem4341148 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341149 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4341148 B) (@lem4341147 B t')). Qed.
Lemma lem4341150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341151 {B : Type'} (t' : B -> Prop) : (term112 B t') = (term112 B t').
Proof. exact (MK_COMB (@lem4341150) (@lem4341149 B t')). Qed.
Lemma lem4341152 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term120 A B s' s t' t) = (term120 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341151 B t') (@lem4341143 A B s' s t' t)). Qed.
Lemma lem4341155 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4341156 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4341155 A s' x)). Qed.
Lemma lem4341157 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341158 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4341157 A) (@lem4341156 A s')). Qed.
Lemma lem4341159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341160 {A : Type'} (s' : A -> Prop) : (term112 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4341159) (@lem4341158 A s')). Qed.
Lemma lem4341161 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term121 A B s' s t' t) = (term121 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341160 A s') (@lem4341152 A B s' s t' t)). Qed.
Lemma lem4341166 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term114 B t t' x) = (term114 B t t' x).
Proof. exact (eq_refl (term114 B t t' x)). Qed.
Lemma lem4341167 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term116 B t t') = (term116 B t t').
Proof. exact (fun_ext (fun x : B => @lem4341166 B t t' x)). Qed.
Lemma lem4341168 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341169 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term117 B t t') = (term117 B t t').
Proof. exact (MK_COMB (@lem4341168 B) (@lem4341167 B t t')). Qed.
Lemma lem4341174 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term114 A s s' x) = (term114 A s s' x).
Proof. exact (eq_refl (term114 A s s' x)). Qed.
Lemma lem4341175 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term116 A s s') = (term116 A s s').
Proof. exact (fun_ext (fun x : A => @lem4341174 A s s' x)). Qed.
Lemma lem4341176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341177 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term117 A s s') = (term117 A s s').
Proof. exact (MK_COMB (@lem4341176 A) (@lem4341175 A s s')). Qed.
Lemma lem4341178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341179 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term118 A s s') = (term118 A s s').
Proof. exact (MK_COMB (@lem4341178) (@lem4341177 A s s')). Qed.
Lemma lem4341180 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term119 A B s s' t t') = (term119 A B s s' t t').
Proof. exact (MK_COMB (@lem4341179 A s s') (@lem4341169 B t t')). Qed.
Lemma lem4341183 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4341184 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4341183 B t x)). Qed.
Lemma lem4341185 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341186 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4341185 B) (@lem4341184 B t)). Qed.
Lemma lem4341187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341188 {B : Type'} (t : B -> Prop) : (term112 B t) = (term112 B t).
Proof. exact (MK_COMB (@lem4341187) (@lem4341186 B t)). Qed.
Lemma lem4341189 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term120 A B s s' t t') = (term120 A B s s' t t').
Proof. exact (MK_COMB (@lem4341188 B t) (@lem4341180 A B s s' t t')). Qed.
Lemma lem4341192 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4341193 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4341192 A s x)). Qed.
Lemma lem4341194 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341195 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4341194 A) (@lem4341193 A s)). Qed.
Lemma lem4341196 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341197 {A : Type'} (s : A -> Prop) : (term112 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4341196) (@lem4341195 A s)). Qed.
Lemma lem4341198 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term121 A B s s' t t') = (term121 A B s s' t t').
Proof. exact (MK_COMB (@lem4341197 A s) (@lem4341189 A B s s' t t')). Qed.
Lemma lem4341199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341200 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term122 A B s s' t t') = (term122 A B s s' t t').
Proof. exact (MK_COMB (@lem4341199) (@lem4341198 A B s s' t t')). Qed.
Lemma lem4341201 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term123 A B s' s t' t) = (term123 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341200 A B s s' t t') (@lem4341161 A B s' s t' t)). Qed.
Lemma lem4341202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4341203 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term124 A B s' s t' t) = (term124 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341202) (@lem4341201 A B s' s t' t)). Qed.
Lemma lem4341204 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term123 A B s' s t' t) = (term132 A B s' s t' t)) = ((term123 A B s' s t' t) = (term132 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4341203 A B s' s t' t) (@lem4341124 A B s' s t' t)). Qed.
Lemma lem4341205 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term133 A B s' s t) = (term133 A B s' s t).
Proof. exact (fun_ext (fun t' : B -> Prop => @lem4341204 A B s' s t' t)). Qed.
Lemma lem4341206 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4341207 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : (term134 A B s' s t) = (term134 A B s' s t).
Proof. exact (MK_COMB (@lem4341206 B) (@lem4341205 A B s' s t)). Qed.
Lemma lem4341208 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term135 A B s' s) = (term135 A B s' s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4341207 A B s' s t)). Qed.
Lemma lem4341209 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4341210 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : (term136 A B s' s) = (term136 A B s' s).
Proof. exact (MK_COMB (@lem4341209 B) (@lem4341208 A B s' s)). Qed.
Lemma lem4341211 {A B : Type'} (s : A -> Prop) : (term137 A B s) = (term137 A B s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem4341210 A B s' s)). Qed.
Lemma lem4341212 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4341213 {A B : Type'} (s : A -> Prop) : (term138 A B s) = (term138 A B s).
Proof. exact (MK_COMB (@lem4341212 A) (@lem4341211 A B s)). Qed.
Lemma lem4341214 {A B : Type'} : (term139 A B) = (term139 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4341213 A B s)). Qed.
Lemma lem4341215 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4341216 {A B : Type'} : (term140 A B) = (term140 A B).
Proof. exact (MK_COMB (@lem4341215 A) (@lem4341214 A B)). Qed.
Lemma lem4341383 {A B : Type'} : (term142 A B) = (term140 A B).
Proof. exact (TRANS (@lem4341047 A B) (@lem4341216 A B)). Qed.
Lemma lem4341384 {A B : Type'} : (term140 A B) = (term142 A B).
Proof. exact (SYM (@lem4341383 A B)). Qed.
Lemma lem4341386 (p : Prop) : p = (term141 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4341387 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term123 A B s' s t' t) = (term132 A B s' s t' t)) = (term149 A B s' s t' t).
Proof. exact (@lem4341386 ((term123 A B s' s t' t) = (term132 A B s' s t' t))). Qed.
Lemma lem4341388 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term149 A B s' s t' t) = ((term123 A B s' s t' t) = (term132 A B s' s t' t)).
Proof. exact (SYM (@lem4341387 A B s' s t' t)). Qed.
Lemma lem4341389 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term150 A B s' s t' t) : term150 A B s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4341390 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4341393 {A : Type'} (s : A -> Prop) (x : A) : (term151 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4341394 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341395 {A : Type'} (s : A -> Prop) : (term154 A s) = (term155 A s).
Proof. exact (@lem4341394 A (term101 A s)). Qed.
Lemma lem4341396 {A : Type'} (s : A -> Prop) (x : A) : (term156 A s x) = (term99 A s x).
Proof. exact (eq_refl (term156 A s x)). Qed.
Lemma lem4341397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341398 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term151 A s x).
Proof. exact (MK_COMB (@lem4341397) (@lem4341396 A s x)). Qed.
Lemma lem4341399 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (s x).
Proof. exact (TRANS (@lem4341398 A s x) (@lem4341393 A s x)). Qed.
Lemma lem4341400 {A : Type'} (s : A -> Prop) : (term158 A s) = (term159 A s).
Proof. exact (fun_ext (fun x : A => @lem4341399 A s x)). Qed.
Lemma lem4341401 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341402 {A : Type'} (s : A -> Prop) : (term155 A s) = (term160 A s).
Proof. exact (MK_COMB (@lem4341401 A) (@lem4341400 A s)). Qed.
Lemma lem4341403 {A : Type'} (s : A -> Prop) : (term154 A s) = (term160 A s).
Proof. exact (TRANS (@lem4341395 A s) (@lem4341402 A s)). Qed.
Lemma lem4341404 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4341390 A s x)). Qed.
Lemma lem4341405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341406 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4341405 A) (@lem4341404 A s)). Qed.
Lemma lem4341407 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4341410 {B : Type'} (t : B -> Prop) (x : B) : (term151 B t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4341411 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341412 {B : Type'} (t : B -> Prop) : (term154 B t) = (term155 B t).
Proof. exact (@lem4341411 B (term101 B t)). Qed.
Lemma lem4341413 {B : Type'} (t : B -> Prop) (x : B) : (term156 B t x) = (term99 B t x).
Proof. exact (eq_refl (term156 B t x)). Qed.
Lemma lem4341414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341415 {B : Type'} (t : B -> Prop) (x : B) : (term157 B t x) = (term151 B t x).
Proof. exact (MK_COMB (@lem4341414) (@lem4341413 B t x)). Qed.
Lemma lem4341416 {B : Type'} (t : B -> Prop) (x : B) : (term157 B t x) = (t x).
Proof. exact (TRANS (@lem4341415 B t x) (@lem4341410 B t x)). Qed.
Lemma lem4341417 {B : Type'} (t : B -> Prop) : (term158 B t) = (term159 B t).
Proof. exact (fun_ext (fun x : B => @lem4341416 B t x)). Qed.
Lemma lem4341418 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341419 {B : Type'} (t : B -> Prop) : (term155 B t) = (term160 B t).
Proof. exact (MK_COMB (@lem4341418 B) (@lem4341417 B t)). Qed.
Lemma lem4341420 {B : Type'} (t : B -> Prop) : (term154 B t) = (term160 B t).
Proof. exact (TRANS (@lem4341412 B t) (@lem4341419 B t)). Qed.
Lemma lem4341421 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4341407 B t x)). Qed.
Lemma lem4341422 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341423 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4341422 B) (@lem4341421 B t)). Qed.
Lemma lem4341432 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term161 A s s' x) = (term162 A s s' x).
Proof. exact (@lem17362 (s x) (s' x)). Qed.
Lemma lem4341437 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term114 A s s' x) = (term163 A s s' x).
Proof. exact (@lem17265 (s x) (s' x)). Qed.
Lemma lem4341438 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341439 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term164 A s s') = (term165 A s s').
Proof. exact (@lem4341438 A (term116 A s s')). Qed.
Lemma lem4341440 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term166 A s s' x) = (term114 A s s' x).
Proof. exact (eq_refl (term166 A s s' x)). Qed.
Lemma lem4341441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341442 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term167 A s s' x) = (term161 A s s' x).
Proof. exact (MK_COMB (@lem4341441) (@lem4341440 A s s' x)). Qed.
Lemma lem4341443 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term167 A s s' x) = (term162 A s s' x).
Proof. exact (TRANS (@lem4341442 A s s' x) (@lem4341432 A s s' x)). Qed.
Lemma lem4341444 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term168 A s s') = (term169 A s s').
Proof. exact (fun_ext (fun x : A => @lem4341443 A s s' x)). Qed.
Lemma lem4341445 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341446 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term165 A s s') = (term170 A s s').
Proof. exact (MK_COMB (@lem4341445 A) (@lem4341444 A s s')). Qed.
Lemma lem4341447 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term164 A s s') = (term170 A s s').
Proof. exact (TRANS (@lem4341439 A s s') (@lem4341446 A s s')). Qed.
Lemma lem4341448 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term116 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4341437 A s s' x)). Qed.
Lemma lem4341449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341450 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term117 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4341449 A) (@lem4341448 A s s')). Qed.
Lemma lem4341459 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term161 B t t' x) = (term162 B t t' x).
Proof. exact (@lem17362 (t x) (t' x)). Qed.
Lemma lem4341464 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term114 B t t' x) = (term163 B t t' x).
Proof. exact (@lem17265 (t x) (t' x)). Qed.
Lemma lem4341465 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341466 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term164 B t t') = (term165 B t t').
Proof. exact (@lem4341465 B (term116 B t t')). Qed.
Lemma lem4341467 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term166 B t t' x) = (term114 B t t' x).
Proof. exact (eq_refl (term166 B t t' x)). Qed.
Lemma lem4341468 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341469 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term167 B t t' x) = (term161 B t t' x).
Proof. exact (MK_COMB (@lem4341468) (@lem4341467 B t t' x)). Qed.
Lemma lem4341470 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term167 B t t' x) = (term162 B t t' x).
Proof. exact (TRANS (@lem4341469 B t t' x) (@lem4341459 B t t' x)). Qed.
Lemma lem4341471 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term168 B t t') = (term169 B t t').
Proof. exact (fun_ext (fun x : B => @lem4341470 B t t' x)). Qed.
Lemma lem4341472 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341473 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term165 B t t') = (term170 B t t').
Proof. exact (MK_COMB (@lem4341472 B) (@lem4341471 B t t')). Qed.
Lemma lem4341474 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term164 B t t') = (term170 B t t').
Proof. exact (TRANS (@lem4341466 B t t') (@lem4341473 B t t')). Qed.
Lemma lem4341475 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term116 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4341464 B t t' x)). Qed.
Lemma lem4341476 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341477 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term117 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4341476 B) (@lem4341475 B t t')). Qed.
Lemma lem4341478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341479 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term173 A s s') = (term174 A s s').
Proof. exact (MK_COMB (@lem4341478) (@lem4341447 A s s')). Qed.
Lemma lem4341480 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term175 A B s s' t t') = (term176 A B s s' t t').
Proof. exact (MK_COMB (@lem4341479 A s s') (@lem4341474 B t t')). Qed.
Lemma lem4341481 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term177 A B s s' t t') = (term175 A B s s' t t').
Proof. exact (@lem17045 (term117 A s s') (term117 B t t')). Qed.
Lemma lem4341482 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term177 A B s s' t t') = (term176 A B s s' t t').
Proof. exact (TRANS (@lem4341481 A B s s' t t') (@lem4341480 A B s s' t t')). Qed.
Lemma lem4341483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341484 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term118 A s s') = (term178 A s s').
Proof. exact (MK_COMB (@lem4341483) (@lem4341450 A s s')). Qed.
Lemma lem4341485 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term119 A B s s' t t') = (term179 A B s s' t t').
Proof. exact (MK_COMB (@lem4341484 A s s') (@lem4341477 B t t')). Qed.
Lemma lem4341486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341487 {B : Type'} (t : B -> Prop) : (term180 B t) = (term181 B t).
Proof. exact (MK_COMB (@lem4341486) (@lem4341420 B t)). Qed.
Lemma lem4341488 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term182 A B s s' t t') = (term183 A B s s' t t').
Proof. exact (MK_COMB (@lem4341487 B t) (@lem4341482 A B s s' t t')). Qed.
Lemma lem4341489 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term184 A B s s' t t') = (term182 A B s s' t t').
Proof. exact (@lem17160 (term102 B t) (term119 A B s s' t t')). Qed.
Lemma lem4341490 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term184 A B s s' t t') = (term183 A B s s' t t').
Proof. exact (TRANS (@lem4341489 A B s s' t t') (@lem4341488 A B s s' t t')). Qed.
Lemma lem4341491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341492 {B : Type'} (t : B -> Prop) : (term112 B t) = (term112 B t).
Proof. exact (MK_COMB (@lem4341491) (@lem4341423 B t)). Qed.
Lemma lem4341493 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term120 A B s s' t t') = (term185 A B s s' t t').
Proof. exact (MK_COMB (@lem4341492 B t) (@lem4341485 A B s s' t t')). Qed.
Lemma lem4341494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341495 {A : Type'} (s : A -> Prop) : (term180 A s) = (term181 A s).
Proof. exact (MK_COMB (@lem4341494) (@lem4341403 A s)). Qed.
Lemma lem4341496 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term186 A B s s' t t') = (term187 A B s s' t t').
Proof. exact (MK_COMB (@lem4341495 A s) (@lem4341490 A B s s' t t')). Qed.
Lemma lem4341497 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term188 A B s s' t t') = (term186 A B s s' t t').
Proof. exact (@lem17160 (term102 A s) (term120 A B s s' t t')). Qed.
Lemma lem4341498 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term188 A B s s' t t') = (term187 A B s s' t t').
Proof. exact (TRANS (@lem4341497 A B s s' t t') (@lem4341496 A B s s' t t')). Qed.
Lemma lem4341499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341500 {A : Type'} (s : A -> Prop) : (term112 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4341499) (@lem4341406 A s)). Qed.
Lemma lem4341501 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term121 A B s s' t t') = (term189 A B s s' t t').
Proof. exact (MK_COMB (@lem4341500 A s) (@lem4341493 A B s s' t t')). Qed.
Lemma lem4341502 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4341505 {A : Type'} (s' : A -> Prop) (x : A) : (term151 A s' x) = (s' x).
Proof. exact (@lem16933 (s' x)). Qed.
Lemma lem4341506 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341507 {A : Type'} (s' : A -> Prop) : (term154 A s') = (term155 A s').
Proof. exact (@lem4341506 A (term101 A s')). Qed.
Lemma lem4341508 {A : Type'} (s' : A -> Prop) (x : A) : (term156 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term156 A s' x)). Qed.
Lemma lem4341509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341510 {A : Type'} (s' : A -> Prop) (x : A) : (term157 A s' x) = (term151 A s' x).
Proof. exact (MK_COMB (@lem4341509) (@lem4341508 A s' x)). Qed.
Lemma lem4341511 {A : Type'} (s' : A -> Prop) (x : A) : (term157 A s' x) = (s' x).
Proof. exact (TRANS (@lem4341510 A s' x) (@lem4341505 A s' x)). Qed.
Lemma lem4341512 {A : Type'} (s' : A -> Prop) : (term158 A s') = (term159 A s').
Proof. exact (fun_ext (fun x : A => @lem4341511 A s' x)). Qed.
Lemma lem4341513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341514 {A : Type'} (s' : A -> Prop) : (term155 A s') = (term160 A s').
Proof. exact (MK_COMB (@lem4341513 A) (@lem4341512 A s')). Qed.
Lemma lem4341515 {A : Type'} (s' : A -> Prop) : (term154 A s') = (term160 A s').
Proof. exact (TRANS (@lem4341507 A s') (@lem4341514 A s')). Qed.
Lemma lem4341516 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4341502 A s' x)). Qed.
Lemma lem4341517 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341518 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4341517 A) (@lem4341516 A s')). Qed.
Lemma lem4341519 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4341522 {B : Type'} (t' : B -> Prop) (x : B) : (term151 B t' x) = (t' x).
Proof. exact (@lem16933 (t' x)). Qed.
Lemma lem4341523 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341524 {B : Type'} (t' : B -> Prop) : (term154 B t') = (term155 B t').
Proof. exact (@lem4341523 B (term101 B t')). Qed.
Lemma lem4341525 {B : Type'} (t' : B -> Prop) (x : B) : (term156 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term156 B t' x)). Qed.
Lemma lem4341526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341527 {B : Type'} (t' : B -> Prop) (x : B) : (term157 B t' x) = (term151 B t' x).
Proof. exact (MK_COMB (@lem4341526) (@lem4341525 B t' x)). Qed.
Lemma lem4341528 {B : Type'} (t' : B -> Prop) (x : B) : (term157 B t' x) = (t' x).
Proof. exact (TRANS (@lem4341527 B t' x) (@lem4341522 B t' x)). Qed.
Lemma lem4341529 {B : Type'} (t' : B -> Prop) : (term158 B t') = (term159 B t').
Proof. exact (fun_ext (fun x : B => @lem4341528 B t' x)). Qed.
Lemma lem4341530 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341531 {B : Type'} (t' : B -> Prop) : (term155 B t') = (term160 B t').
Proof. exact (MK_COMB (@lem4341530 B) (@lem4341529 B t')). Qed.
Lemma lem4341532 {B : Type'} (t' : B -> Prop) : (term154 B t') = (term160 B t').
Proof. exact (TRANS (@lem4341524 B t') (@lem4341531 B t')). Qed.
Lemma lem4341533 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4341519 B t' x)). Qed.
Lemma lem4341534 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341535 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4341534 B) (@lem4341533 B t')). Qed.
Lemma lem4341544 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term161 A s' s x) = (term162 A s' s x).
Proof. exact (@lem17362 (s' x) (s x)). Qed.
Lemma lem4341549 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term114 A s' s x) = (term163 A s' s x).
Proof. exact (@lem17265 (s' x) (s x)). Qed.
Lemma lem4341550 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341551 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term164 A s' s) = (term165 A s' s).
Proof. exact (@lem4341550 A (term116 A s' s)). Qed.
Lemma lem4341552 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term166 A s' s x) = (term114 A s' s x).
Proof. exact (eq_refl (term166 A s' s x)). Qed.
Lemma lem4341553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341554 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term167 A s' s x) = (term161 A s' s x).
Proof. exact (MK_COMB (@lem4341553) (@lem4341552 A s' s x)). Qed.
Lemma lem4341555 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term167 A s' s x) = (term162 A s' s x).
Proof. exact (TRANS (@lem4341554 A s' s x) (@lem4341544 A s' s x)). Qed.
Lemma lem4341556 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term168 A s' s) = (term169 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4341555 A s' s x)). Qed.
Lemma lem4341557 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341558 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term165 A s' s) = (term170 A s' s).
Proof. exact (MK_COMB (@lem4341557 A) (@lem4341556 A s' s)). Qed.
Lemma lem4341559 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term164 A s' s) = (term170 A s' s).
Proof. exact (TRANS (@lem4341551 A s' s) (@lem4341558 A s' s)). Qed.
Lemma lem4341560 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term116 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4341549 A s' s x)). Qed.
Lemma lem4341561 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341562 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term117 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4341561 A) (@lem4341560 A s' s)). Qed.
Lemma lem4341571 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term161 B t' t x) = (term162 B t' t x).
Proof. exact (@lem17362 (t' x) (t x)). Qed.
Lemma lem4341576 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term114 B t' t x) = (term163 B t' t x).
Proof. exact (@lem17265 (t' x) (t x)). Qed.
Lemma lem4341577 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341578 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term164 B t' t) = (term165 B t' t).
Proof. exact (@lem4341577 B (term116 B t' t)). Qed.
Lemma lem4341579 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term166 B t' t x) = (term114 B t' t x).
Proof. exact (eq_refl (term166 B t' t x)). Qed.
Lemma lem4341580 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341581 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term167 B t' t x) = (term161 B t' t x).
Proof. exact (MK_COMB (@lem4341580) (@lem4341579 B t' t x)). Qed.
Lemma lem4341582 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term167 B t' t x) = (term162 B t' t x).
Proof. exact (TRANS (@lem4341581 B t' t x) (@lem4341571 B t' t x)). Qed.
Lemma lem4341583 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term168 B t' t) = (term169 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4341582 B t' t x)). Qed.
Lemma lem4341584 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341585 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term165 B t' t) = (term170 B t' t).
Proof. exact (MK_COMB (@lem4341584 B) (@lem4341583 B t' t)). Qed.
Lemma lem4341586 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term164 B t' t) = (term170 B t' t).
Proof. exact (TRANS (@lem4341578 B t' t) (@lem4341585 B t' t)). Qed.
Lemma lem4341587 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term116 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4341576 B t' t x)). Qed.
Lemma lem4341588 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341589 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term117 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4341588 B) (@lem4341587 B t' t)). Qed.
Lemma lem4341590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341591 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term173 A s' s) = (term174 A s' s).
Proof. exact (MK_COMB (@lem4341590) (@lem4341559 A s' s)). Qed.
Lemma lem4341592 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term175 A B s' s t' t) = (term176 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341591 A s' s) (@lem4341586 B t' t)). Qed.
Lemma lem4341593 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term177 A B s' s t' t) = (term175 A B s' s t' t).
Proof. exact (@lem17045 (term117 A s' s) (term117 B t' t)). Qed.
Lemma lem4341594 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term177 A B s' s t' t) = (term176 A B s' s t' t).
Proof. exact (TRANS (@lem4341593 A B s' s t' t) (@lem4341592 A B s' s t' t)). Qed.
Lemma lem4341595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341596 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term118 A s' s) = (term178 A s' s).
Proof. exact (MK_COMB (@lem4341595) (@lem4341562 A s' s)). Qed.
Lemma lem4341597 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term119 A B s' s t' t) = (term179 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341596 A s' s) (@lem4341589 B t' t)). Qed.
Lemma lem4341598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341599 {B : Type'} (t' : B -> Prop) : (term180 B t') = (term181 B t').
Proof. exact (MK_COMB (@lem4341598) (@lem4341532 B t')). Qed.
Lemma lem4341600 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term182 A B s' s t' t) = (term183 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341599 B t') (@lem4341594 A B s' s t' t)). Qed.
Lemma lem4341601 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term184 A B s' s t' t) = (term182 A B s' s t' t).
Proof. exact (@lem17160 (term102 B t') (term119 A B s' s t' t)). Qed.
Lemma lem4341602 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term184 A B s' s t' t) = (term183 A B s' s t' t).
Proof. exact (TRANS (@lem4341601 A B s' s t' t) (@lem4341600 A B s' s t' t)). Qed.
Lemma lem4341603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341604 {B : Type'} (t' : B -> Prop) : (term112 B t') = (term112 B t').
Proof. exact (MK_COMB (@lem4341603) (@lem4341535 B t')). Qed.
Lemma lem4341605 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term120 A B s' s t' t) = (term185 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341604 B t') (@lem4341597 A B s' s t' t)). Qed.
Lemma lem4341606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341607 {A : Type'} (s' : A -> Prop) : (term180 A s') = (term181 A s').
Proof. exact (MK_COMB (@lem4341606) (@lem4341515 A s')). Qed.
Lemma lem4341608 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term186 A B s' s t' t) = (term187 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341607 A s') (@lem4341602 A B s' s t' t)). Qed.
Lemma lem4341609 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term188 A B s' s t' t) = (term186 A B s' s t' t).
Proof. exact (@lem17160 (term102 A s') (term120 A B s' s t' t)). Qed.
Lemma lem4341610 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term188 A B s' s t' t) = (term187 A B s' s t' t).
Proof. exact (TRANS (@lem4341609 A B s' s t' t) (@lem4341608 A B s' s t' t)). Qed.
Lemma lem4341611 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341612 {A : Type'} (s' : A -> Prop) : (term112 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4341611) (@lem4341518 A s')). Qed.
Lemma lem4341613 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term121 A B s' s t' t) = (term189 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341612 A s') (@lem4341605 A B s' s t' t)). Qed.
Lemma lem4341614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341615 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term190 A B s s' t t') = (term191 A B s s' t t').
Proof. exact (MK_COMB (@lem4341614) (@lem4341498 A B s s' t t')). Qed.
Lemma lem4341616 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term192 A B s' s t' t) = (term193 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341615 A B s s' t t') (@lem4341610 A B s' s t' t)). Qed.
Lemma lem4341617 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term194 A B s' s t' t) = (term192 A B s' s t' t).
Proof. exact (@lem17045 (term121 A B s s' t t') (term121 A B s' s t' t)). Qed.
Lemma lem4341618 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term194 A B s' s t' t) = (term193 A B s' s t' t).
Proof. exact (TRANS (@lem4341617 A B s' s t' t) (@lem4341616 A B s' s t' t)). Qed.
Lemma lem4341619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341620 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term122 A B s s' t t') = (term195 A B s s' t t').
Proof. exact (MK_COMB (@lem4341619) (@lem4341501 A B s s' t t')). Qed.
Lemma lem4341621 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term123 A B s' s t' t) = (term196 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341620 A B s s' t t') (@lem4341613 A B s' s t' t)). Qed.
Lemma lem4341622 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4341625 {A : Type'} (s : A -> Prop) (x : A) : (term151 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4341626 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341627 {A : Type'} (s : A -> Prop) : (term154 A s) = (term155 A s).
Proof. exact (@lem4341626 A (term101 A s)). Qed.
Lemma lem4341628 {A : Type'} (s : A -> Prop) (x : A) : (term156 A s x) = (term99 A s x).
Proof. exact (eq_refl (term156 A s x)). Qed.
Lemma lem4341629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341630 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (term151 A s x).
Proof. exact (MK_COMB (@lem4341629) (@lem4341628 A s x)). Qed.
Lemma lem4341631 {A : Type'} (s : A -> Prop) (x : A) : (term157 A s x) = (s x).
Proof. exact (TRANS (@lem4341630 A s x) (@lem4341625 A s x)). Qed.
Lemma lem4341632 {A : Type'} (s : A -> Prop) : (term158 A s) = (term159 A s).
Proof. exact (fun_ext (fun x : A => @lem4341631 A s x)). Qed.
Lemma lem4341633 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341634 {A : Type'} (s : A -> Prop) : (term155 A s) = (term160 A s).
Proof. exact (MK_COMB (@lem4341633 A) (@lem4341632 A s)). Qed.
Lemma lem4341635 {A : Type'} (s : A -> Prop) : (term154 A s) = (term160 A s).
Proof. exact (TRANS (@lem4341627 A s) (@lem4341634 A s)). Qed.
Lemma lem4341636 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4341622 A s x)). Qed.
Lemma lem4341637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341638 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4341637 A) (@lem4341636 A s)). Qed.
Lemma lem4341639 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4341642 {B : Type'} (t : B -> Prop) (x : B) : (term151 B t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem4341643 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341644 {B : Type'} (t : B -> Prop) : (term154 B t) = (term155 B t).
Proof. exact (@lem4341643 B (term101 B t)). Qed.
Lemma lem4341645 {B : Type'} (t : B -> Prop) (x : B) : (term156 B t x) = (term99 B t x).
Proof. exact (eq_refl (term156 B t x)). Qed.
Lemma lem4341646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341647 {B : Type'} (t : B -> Prop) (x : B) : (term157 B t x) = (term151 B t x).
Proof. exact (MK_COMB (@lem4341646) (@lem4341645 B t x)). Qed.
Lemma lem4341648 {B : Type'} (t : B -> Prop) (x : B) : (term157 B t x) = (t x).
Proof. exact (TRANS (@lem4341647 B t x) (@lem4341642 B t x)). Qed.
Lemma lem4341649 {B : Type'} (t : B -> Prop) : (term158 B t) = (term159 B t).
Proof. exact (fun_ext (fun x : B => @lem4341648 B t x)). Qed.
Lemma lem4341650 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341651 {B : Type'} (t : B -> Prop) : (term155 B t) = (term160 B t).
Proof. exact (MK_COMB (@lem4341650 B) (@lem4341649 B t)). Qed.
Lemma lem4341652 {B : Type'} (t : B -> Prop) : (term154 B t) = (term160 B t).
Proof. exact (TRANS (@lem4341644 B t) (@lem4341651 B t)). Qed.
Lemma lem4341653 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4341639 B t x)). Qed.
Lemma lem4341654 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341655 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4341654 B) (@lem4341653 B t)). Qed.
Lemma lem4341656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341657 {A : Type'} (s : A -> Prop) : (term180 A s) = (term181 A s).
Proof. exact (MK_COMB (@lem4341656) (@lem4341635 A s)). Qed.
Lemma lem4341658 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term197 A B s t) = (term198 A B s t).
Proof. exact (MK_COMB (@lem4341657 A s) (@lem4341652 B t)). Qed.
Lemma lem4341659 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term199 A B s t) = (term197 A B s t).
Proof. exact (@lem17160 (term102 A s) (term102 B t)). Qed.
Lemma lem4341660 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term199 A B s t) = (term198 A B s t).
Proof. exact (TRANS (@lem4341659 A B s t) (@lem4341658 A B s t)). Qed.
Lemma lem4341661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341662 {A : Type'} (s : A -> Prop) : (term112 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4341661) (@lem4341638 A s)). Qed.
Lemma lem4341663 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term125 A B s t) = (term125 A B s t).
Proof. exact (MK_COMB (@lem4341662 A s) (@lem4341655 B t)). Qed.
Lemma lem4341664 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4341667 {A : Type'} (s' : A -> Prop) (x : A) : (term151 A s' x) = (s' x).
Proof. exact (@lem16933 (s' x)). Qed.
Lemma lem4341668 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341669 {A : Type'} (s' : A -> Prop) : (term154 A s') = (term155 A s').
Proof. exact (@lem4341668 A (term101 A s')). Qed.
Lemma lem4341670 {A : Type'} (s' : A -> Prop) (x : A) : (term156 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term156 A s' x)). Qed.
Lemma lem4341671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341672 {A : Type'} (s' : A -> Prop) (x : A) : (term157 A s' x) = (term151 A s' x).
Proof. exact (MK_COMB (@lem4341671) (@lem4341670 A s' x)). Qed.
Lemma lem4341673 {A : Type'} (s' : A -> Prop) (x : A) : (term157 A s' x) = (s' x).
Proof. exact (TRANS (@lem4341672 A s' x) (@lem4341667 A s' x)). Qed.
Lemma lem4341674 {A : Type'} (s' : A -> Prop) : (term158 A s') = (term159 A s').
Proof. exact (fun_ext (fun x : A => @lem4341673 A s' x)). Qed.
Lemma lem4341675 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341676 {A : Type'} (s' : A -> Prop) : (term155 A s') = (term160 A s').
Proof. exact (MK_COMB (@lem4341675 A) (@lem4341674 A s')). Qed.
Lemma lem4341677 {A : Type'} (s' : A -> Prop) : (term154 A s') = (term160 A s').
Proof. exact (TRANS (@lem4341669 A s') (@lem4341676 A s')). Qed.
Lemma lem4341678 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4341664 A s' x)). Qed.
Lemma lem4341679 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341680 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4341679 A) (@lem4341678 A s')). Qed.
Lemma lem4341681 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4341684 {B : Type'} (t' : B -> Prop) (x : B) : (term151 B t' x) = (t' x).
Proof. exact (@lem16933 (t' x)). Qed.
Lemma lem4341685 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341686 {B : Type'} (t' : B -> Prop) : (term154 B t') = (term155 B t').
Proof. exact (@lem4341685 B (term101 B t')). Qed.
Lemma lem4341687 {B : Type'} (t' : B -> Prop) (x : B) : (term156 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term156 B t' x)). Qed.
Lemma lem4341688 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341689 {B : Type'} (t' : B -> Prop) (x : B) : (term157 B t' x) = (term151 B t' x).
Proof. exact (MK_COMB (@lem4341688) (@lem4341687 B t' x)). Qed.
Lemma lem4341690 {B : Type'} (t' : B -> Prop) (x : B) : (term157 B t' x) = (t' x).
Proof. exact (TRANS (@lem4341689 B t' x) (@lem4341684 B t' x)). Qed.
Lemma lem4341691 {B : Type'} (t' : B -> Prop) : (term158 B t') = (term159 B t').
Proof. exact (fun_ext (fun x : B => @lem4341690 B t' x)). Qed.
Lemma lem4341692 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341693 {B : Type'} (t' : B -> Prop) : (term155 B t') = (term160 B t').
Proof. exact (MK_COMB (@lem4341692 B) (@lem4341691 B t')). Qed.
Lemma lem4341694 {B : Type'} (t' : B -> Prop) : (term154 B t') = (term160 B t').
Proof. exact (TRANS (@lem4341686 B t') (@lem4341693 B t')). Qed.
Lemma lem4341695 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4341681 B t' x)). Qed.
Lemma lem4341696 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341697 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4341696 B) (@lem4341695 B t')). Qed.
Lemma lem4341698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341699 {A : Type'} (s' : A -> Prop) : (term180 A s') = (term181 A s').
Proof. exact (MK_COMB (@lem4341698) (@lem4341677 A s')). Qed.
Lemma lem4341700 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term197 A B s' t') = (term198 A B s' t').
Proof. exact (MK_COMB (@lem4341699 A s') (@lem4341694 B t')). Qed.
Lemma lem4341701 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term199 A B s' t') = (term197 A B s' t').
Proof. exact (@lem17160 (term102 A s') (term102 B t')). Qed.
Lemma lem4341702 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term199 A B s' t') = (term198 A B s' t').
Proof. exact (TRANS (@lem4341701 A B s' t') (@lem4341700 A B s' t')). Qed.
Lemma lem4341703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341704 {A : Type'} (s' : A -> Prop) : (term112 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4341703) (@lem4341680 A s')). Qed.
Lemma lem4341705 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term125 A B s' t') = (term125 A B s' t').
Proof. exact (MK_COMB (@lem4341704 A s') (@lem4341697 B t')). Qed.
Lemma lem4341706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341707 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term200 A B s t) = (term201 A B s t).
Proof. exact (MK_COMB (@lem4341706) (@lem4341660 A B s t)). Qed.
Lemma lem4341708 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term202 A B s t s' t') = (term203 A B s t s' t').
Proof. exact (MK_COMB (@lem4341707 A B s t) (@lem4341702 A B s' t')). Qed.
Lemma lem4341709 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term204 A B s t s' t') = (term202 A B s t s' t').
Proof. exact (@lem17045 (term125 A B s t) (term125 A B s' t')). Qed.
Lemma lem4341710 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term204 A B s t s' t') = (term203 A B s t s' t').
Proof. exact (TRANS (@lem4341709 A B s t s' t') (@lem4341708 A B s t s' t')). Qed.
Lemma lem4341711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341712 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term126 A B s t) = (term126 A B s t).
Proof. exact (MK_COMB (@lem4341711) (@lem4341663 A B s t)). Qed.
Lemma lem4341713 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term127 A B s t s' t') = (term127 A B s t s' t').
Proof. exact (MK_COMB (@lem4341712 A B s t) (@lem4341705 A B s' t')). Qed.
Lemma lem4341722 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term161 A s s' x) = (term162 A s s' x).
Proof. exact (@lem17362 (s x) (s' x)). Qed.
Lemma lem4341727 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term114 A s s' x) = (term163 A s s' x).
Proof. exact (@lem17265 (s x) (s' x)). Qed.
Lemma lem4341728 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341729 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term164 A s s') = (term165 A s s').
Proof. exact (@lem4341728 A (term116 A s s')). Qed.
Lemma lem4341730 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term166 A s s' x) = (term114 A s s' x).
Proof. exact (eq_refl (term166 A s s' x)). Qed.
Lemma lem4341731 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341732 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term167 A s s' x) = (term161 A s s' x).
Proof. exact (MK_COMB (@lem4341731) (@lem4341730 A s s' x)). Qed.
Lemma lem4341733 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term167 A s s' x) = (term162 A s s' x).
Proof. exact (TRANS (@lem4341732 A s s' x) (@lem4341722 A s s' x)). Qed.
Lemma lem4341734 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term168 A s s') = (term169 A s s').
Proof. exact (fun_ext (fun x : A => @lem4341733 A s s' x)). Qed.
Lemma lem4341735 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341736 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term165 A s s') = (term170 A s s').
Proof. exact (MK_COMB (@lem4341735 A) (@lem4341734 A s s')). Qed.
Lemma lem4341737 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term164 A s s') = (term170 A s s').
Proof. exact (TRANS (@lem4341729 A s s') (@lem4341736 A s s')). Qed.
Lemma lem4341738 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term116 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4341727 A s s' x)). Qed.
Lemma lem4341739 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341740 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term117 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4341739 A) (@lem4341738 A s s')). Qed.
Lemma lem4341749 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term161 A s' s x) = (term162 A s' s x).
Proof. exact (@lem17362 (s' x) (s x)). Qed.
Lemma lem4341754 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term114 A s' s x) = (term163 A s' s x).
Proof. exact (@lem17265 (s' x) (s x)). Qed.
Lemma lem4341755 {A : Type'} (P : A -> Prop) : (term152 A P) = (term153 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4341756 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term164 A s' s) = (term165 A s' s).
Proof. exact (@lem4341755 A (term116 A s' s)). Qed.
Lemma lem4341757 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term166 A s' s x) = (term114 A s' s x).
Proof. exact (eq_refl (term166 A s' s x)). Qed.
Lemma lem4341758 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341759 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term167 A s' s x) = (term161 A s' s x).
Proof. exact (MK_COMB (@lem4341758) (@lem4341757 A s' s x)). Qed.
Lemma lem4341760 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term167 A s' s x) = (term162 A s' s x).
Proof. exact (TRANS (@lem4341759 A s' s x) (@lem4341749 A s' s x)). Qed.
Lemma lem4341761 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term168 A s' s) = (term169 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4341760 A s' s x)). Qed.
Lemma lem4341762 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4341763 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term165 A s' s) = (term170 A s' s).
Proof. exact (MK_COMB (@lem4341762 A) (@lem4341761 A s' s)). Qed.
Lemma lem4341764 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term164 A s' s) = (term170 A s' s).
Proof. exact (TRANS (@lem4341756 A s' s) (@lem4341763 A s' s)). Qed.
Lemma lem4341765 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term116 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4341754 A s' s x)). Qed.
Lemma lem4341766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4341767 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term117 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4341766 A) (@lem4341765 A s' s)). Qed.
Lemma lem4341768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341769 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term173 A s s') = (term174 A s s').
Proof. exact (MK_COMB (@lem4341768) (@lem4341737 A s s')). Qed.
Lemma lem4341770 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term205 A s' s) = (term206 A s' s).
Proof. exact (MK_COMB (@lem4341769 A s s') (@lem4341764 A s' s)). Qed.
Lemma lem4341771 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term207 A s' s) = (term205 A s' s).
Proof. exact (@lem17045 (term117 A s s') (term117 A s' s)). Qed.
Lemma lem4341772 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term207 A s' s) = (term206 A s' s).
Proof. exact (TRANS (@lem4341771 A s' s) (@lem4341770 A s' s)). Qed.
Lemma lem4341773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341774 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term118 A s s') = (term178 A s s').
Proof. exact (MK_COMB (@lem4341773) (@lem4341740 A s s')). Qed.
Lemma lem4341775 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term129 A s' s) = (term208 A s' s).
Proof. exact (MK_COMB (@lem4341774 A s s') (@lem4341767 A s' s)). Qed.
Lemma lem4341784 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term161 B t t' x) = (term162 B t t' x).
Proof. exact (@lem17362 (t x) (t' x)). Qed.
Lemma lem4341789 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term114 B t t' x) = (term163 B t t' x).
Proof. exact (@lem17265 (t x) (t' x)). Qed.
Lemma lem4341790 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341791 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term164 B t t') = (term165 B t t').
Proof. exact (@lem4341790 B (term116 B t t')). Qed.
Lemma lem4341792 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term166 B t t' x) = (term114 B t t' x).
Proof. exact (eq_refl (term166 B t t' x)). Qed.
Lemma lem4341793 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341794 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term167 B t t' x) = (term161 B t t' x).
Proof. exact (MK_COMB (@lem4341793) (@lem4341792 B t t' x)). Qed.
Lemma lem4341795 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term167 B t t' x) = (term162 B t t' x).
Proof. exact (TRANS (@lem4341794 B t t' x) (@lem4341784 B t t' x)). Qed.
Lemma lem4341796 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term168 B t t') = (term169 B t t').
Proof. exact (fun_ext (fun x : B => @lem4341795 B t t' x)). Qed.
Lemma lem4341797 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341798 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term165 B t t') = (term170 B t t').
Proof. exact (MK_COMB (@lem4341797 B) (@lem4341796 B t t')). Qed.
Lemma lem4341799 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term164 B t t') = (term170 B t t').
Proof. exact (TRANS (@lem4341791 B t t') (@lem4341798 B t t')). Qed.
Lemma lem4341800 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term116 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4341789 B t t' x)). Qed.
Lemma lem4341801 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341802 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term117 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4341801 B) (@lem4341800 B t t')). Qed.
Lemma lem4341811 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term161 B t' t x) = (term162 B t' t x).
Proof. exact (@lem17362 (t' x) (t x)). Qed.
Lemma lem4341816 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term114 B t' t x) = (term163 B t' t x).
Proof. exact (@lem17265 (t' x) (t x)). Qed.
Lemma lem4341817 {B : Type'} (P : B -> Prop) : (term152 B P) = (term153 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem4341818 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term164 B t' t) = (term165 B t' t).
Proof. exact (@lem4341817 B (term116 B t' t)). Qed.
Lemma lem4341819 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term166 B t' t x) = (term114 B t' t x).
Proof. exact (eq_refl (term166 B t' t x)). Qed.
Lemma lem4341820 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4341821 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term167 B t' t x) = (term161 B t' t x).
Proof. exact (MK_COMB (@lem4341820) (@lem4341819 B t' t x)). Qed.
Lemma lem4341822 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term167 B t' t x) = (term162 B t' t x).
Proof. exact (TRANS (@lem4341821 B t' t x) (@lem4341811 B t' t x)). Qed.
Lemma lem4341823 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term168 B t' t) = (term169 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4341822 B t' t x)). Qed.
Lemma lem4341824 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4341825 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term165 B t' t) = (term170 B t' t).
Proof. exact (MK_COMB (@lem4341824 B) (@lem4341823 B t' t)). Qed.
Lemma lem4341826 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term164 B t' t) = (term170 B t' t).
Proof. exact (TRANS (@lem4341818 B t' t) (@lem4341825 B t' t)). Qed.
Lemma lem4341827 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term116 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4341816 B t' t x)). Qed.
Lemma lem4341828 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4341829 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term117 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4341828 B) (@lem4341827 B t' t)). Qed.
Lemma lem4341830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341831 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term173 B t t') = (term174 B t t').
Proof. exact (MK_COMB (@lem4341830) (@lem4341799 B t t')). Qed.
Lemma lem4341832 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term205 B t' t) = (term206 B t' t).
Proof. exact (MK_COMB (@lem4341831 B t t') (@lem4341826 B t' t)). Qed.
Lemma lem4341833 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term207 B t' t) = (term205 B t' t).
Proof. exact (@lem17045 (term117 B t t') (term117 B t' t)). Qed.
Lemma lem4341834 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term207 B t' t) = (term206 B t' t).
Proof. exact (TRANS (@lem4341833 B t' t) (@lem4341832 B t' t)). Qed.
Lemma lem4341835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341836 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term118 B t t') = (term178 B t t').
Proof. exact (MK_COMB (@lem4341835) (@lem4341802 B t t')). Qed.
Lemma lem4341837 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term129 B t' t) = (term208 B t' t).
Proof. exact (MK_COMB (@lem4341836 B t t') (@lem4341829 B t' t)). Qed.
Lemma lem4341838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341839 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term209 A s' s) = (term210 A s' s).
Proof. exact (MK_COMB (@lem4341838) (@lem4341772 A s' s)). Qed.
Lemma lem4341840 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term211 A B s' s t' t) = (term212 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341839 A s' s) (@lem4341834 B t' t)). Qed.
Lemma lem4341841 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term213 A B s' s t' t) = (term211 A B s' s t' t).
Proof. exact (@lem17045 (term129 A s' s) (term129 B t' t)). Qed.
Lemma lem4341842 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term213 A B s' s t' t) = (term212 A B s' s t' t).
Proof. exact (TRANS (@lem4341841 A B s' s t' t) (@lem4341840 A B s' s t' t)). Qed.
Lemma lem4341843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341844 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term130 A s' s) = (term214 A s' s).
Proof. exact (MK_COMB (@lem4341843) (@lem4341775 A s' s)). Qed.
Lemma lem4341845 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term131 A B s' s t' t) = (term215 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341844 A s' s) (@lem4341837 B t' t)). Qed.
Lemma lem4341846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341847 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term216 A B s t s' t') = (term217 A B s t s' t').
Proof. exact (MK_COMB (@lem4341846) (@lem4341710 A B s t s' t')). Qed.
Lemma lem4341848 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term218 A B s' s t' t) = (term219 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341847 A B s t s' t') (@lem4341842 A B s' s t' t)). Qed.
Lemma lem4341849 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term220 A B s' s t' t) = (term218 A B s' s t' t).
Proof. exact (@lem17160 (term127 A B s t s' t') (term131 A B s' s t' t)). Qed.
Lemma lem4341850 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term220 A B s' s t' t) = (term219 A B s' s t' t).
Proof. exact (TRANS (@lem4341849 A B s' s t' t) (@lem4341848 A B s' s t' t)). Qed.
Lemma lem4341851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341852 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term128 A B s t s' t') = (term128 A B s t s' t').
Proof. exact (MK_COMB (@lem4341851) (@lem4341713 A B s t s' t')). Qed.
Lemma lem4341853 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term132 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341852 A B s t s' t') (@lem4341845 A B s' s t' t)). Qed.
Lemma lem4341854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341855 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term222 A B s' s t' t) = (term223 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341854) (@lem4341618 A B s' s t' t)). Qed.
Lemma lem4341856 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term224 A B s' s t' t) = (term225 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341855 A B s' s t' t) (@lem4341853 A B s' s t' t)). Qed.
Lemma lem4341857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4341858 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term226 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341857) (@lem4341621 A B s' s t' t)). Qed.
Lemma lem4341859 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term228 A B s' s t' t) = (term229 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341858 A B s' s t' t) (@lem4341850 A B s' s t' t)). Qed.
Lemma lem4341860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4341861 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term230 A B s' s t' t) = (term231 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341860) (@lem4341859 A B s' s t' t)). Qed.
Lemma lem4341862 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term232 A B s' s t' t) = (term233 A B s' s t' t).
Proof. exact (MK_COMB (@lem4341861 A B s' s t' t) (@lem4341856 A B s' s t' t)). Qed.
Lemma lem4341863 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term150 A B s' s t' t) = (term232 A B s' s t' t).
Proof. exact (@lem17646 (term123 A B s' s t' t) (term132 A B s' s t' t)). Qed.
Lemma lem4341864 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term150 A B s' s t' t) = (term233 A B s' s t' t).
Proof. exact (TRANS (@lem4341863 A B s' s t' t) (@lem4341862 A B s' s t' t)). Qed.
Lemma lem4342411 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4342412 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4342411 A P Q). Qed.
Lemma lem4342413 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term198 A B s t) = (term236 A B s t).
Proof. exact (@lem4342412 A s (term160 B t)). Qed.
Lemma lem4342415 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342416 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342415 B P Q). Qed.
Lemma lem4342417 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : (term239 A B s x t) = (term240 A B s x t).
Proof. exact (@lem4342416 B (s x) t). Qed.
Lemma lem4342418 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term241 A B s t) = (term242 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4342417 A B s x t)). Qed.
Lemma lem4342419 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342420 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term236 A B s t) = (term243 A B s t).
Proof. exact (MK_COMB (@lem4342419 A) (@lem4342418 A B s t)). Qed.
Lemma lem4342421 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term198 A B s t) = (term243 A B s t).
Proof. exact (TRANS (@lem4342413 A B s t) (@lem4342420 A B s t)). Qed.
Lemma lem4342422 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342423 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term201 A B s t) = (term244 A B s t).
Proof. exact (MK_COMB (@lem4342422) (@lem4342421 A B s t)). Qed.
Lemma lem4342425 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4342426 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4342425 A P Q). Qed.
Lemma lem4342427 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term198 A B s' t') = (term236 A B s' t').
Proof. exact (@lem4342426 A s' (term160 B t')). Qed.
Lemma lem4342429 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342430 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342429 B P Q). Qed.
Lemma lem4342431 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term239 A B s' x t') = (term240 A B s' x t').
Proof. exact (@lem4342430 B (s' x) t'). Qed.
Lemma lem4342432 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term241 A B s' t') = (term242 A B s' t').
Proof. exact (fun_ext (fun x : A => @lem4342431 A B s' x t')). Qed.
Lemma lem4342433 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342434 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term236 A B s' t') = (term243 A B s' t').
Proof. exact (MK_COMB (@lem4342433 A) (@lem4342432 A B s' t')). Qed.
Lemma lem4342435 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term198 A B s' t') = (term243 A B s' t').
Proof. exact (TRANS (@lem4342427 A B s' t') (@lem4342434 A B s' t')). Qed.
Lemma lem4342436 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term203 A B s t s' t') = (term245 A B s t s' t').
Proof. exact (MK_COMB (@lem4342423 A B s t) (@lem4342435 A B s' t')). Qed.
Lemma lem4342438 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4342439 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (@lem4342438 A P Q). Qed.
Lemma lem4342440 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term248 A B s t s' t') = (term249 A B s t s' t').
Proof. exact (@lem4342439 A (term242 A B s t) (term242 A B s' t')). Qed.
Lemma lem4342441 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : (term250 A B s t x) = (term240 A B s x t).
Proof. exact (eq_refl (term250 A B s t x)). Qed.
Lemma lem4342442 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term251 A B s t) = (term242 A B s t).
Proof. exact (fun_ext (fun x : A => @lem4342441 A B s x t)). Qed.
Lemma lem4342443 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342444 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term252 A B s t) = (term243 A B s t).
Proof. exact (MK_COMB (@lem4342443 A) (@lem4342442 A B s t)). Qed.
Lemma lem4342445 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342446 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term253 A B s t) = (term244 A B s t).
Proof. exact (MK_COMB (@lem4342445) (@lem4342444 A B s t)). Qed.
Lemma lem4342447 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term250 A B s' t' x) = (term240 A B s' x t').
Proof. exact (eq_refl (term250 A B s' t' x)). Qed.
Lemma lem4342448 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term251 A B s' t') = (term242 A B s' t').
Proof. exact (fun_ext (fun x : A => @lem4342447 A B s' x t')). Qed.
Lemma lem4342449 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342450 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term252 A B s' t') = (term243 A B s' t').
Proof. exact (MK_COMB (@lem4342449 A) (@lem4342448 A B s' t')). Qed.
Lemma lem4342451 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term248 A B s t s' t') = (term245 A B s t s' t').
Proof. exact (MK_COMB (@lem4342446 A B s t) (@lem4342450 A B s' t')). Qed.
Lemma lem4342452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342453 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term254 A B s t s' t') = (term255 A B s t s' t').
Proof. exact (MK_COMB (@lem4342452) (@lem4342451 A B s t s' t')). Qed.
Lemma lem4342454 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : (term250 A B s t x) = (term240 A B s x t).
Proof. exact (eq_refl (term250 A B s t x)). Qed.
Lemma lem4342455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342456 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : (term256 A B s t x) = (term257 A B s x t).
Proof. exact (MK_COMB (@lem4342455) (@lem4342454 A B s x t)). Qed.
Lemma lem4342457 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term250 A B s' t' x) = (term240 A B s' x t').
Proof. exact (eq_refl (term250 A B s' t' x)). Qed.
Lemma lem4342458 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term258 A B s t s' t' x) = (term259 A B s t s' x t').
Proof. exact (MK_COMB (@lem4342456 A B s x t) (@lem4342457 A B s' x t')). Qed.
Lemma lem4342459 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term260 A B s t s' t') = (term261 A B s t s' t').
Proof. exact (fun_ext (fun x : A => @lem4342458 A B s t s' x t')). Qed.
Lemma lem4342460 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342461 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term249 A B s t s' t') = (term262 A B s t s' t').
Proof. exact (MK_COMB (@lem4342460 A) (@lem4342459 A B s t s' t')). Qed.
Lemma lem4342462 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : ((term248 A B s t s' t') = (term249 A B s t s' t')) = ((term245 A B s t s' t') = (term262 A B s t s' t')).
Proof. exact (MK_COMB (@lem4342453 A B s t s' t') (@lem4342461 A B s t s' t')). Qed.
Lemma lem4342463 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term245 A B s t s' t') = (term262 A B s t s' t').
Proof. exact (EQ_MP (@lem4342462 A B s t s' t') (@lem4342440 A B s t s' t')). Qed.
Lemma lem4342465 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4342466 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term246 B P Q) = (term247 B P Q).
Proof. exact (@lem4342465 B P Q). Qed.
Lemma lem4342467 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term263 A B s t s' x t') = (term264 A B s t s' x t').
Proof. exact (@lem4342466 B (term265 A B s x t) (term265 A B s' x t')). Qed.
Lemma lem4342468 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term266 A B s x t x') = (term267 A B s x t x').
Proof. exact (eq_refl (term266 A B s x t x')). Qed.
Lemma lem4342469 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : (term268 A B s x t) = (term265 A B s x t).
Proof. exact (fun_ext (fun x' : B => @lem4342468 A B s x t x')). Qed.
Lemma lem4342470 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342471 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : (term269 A B s x t) = (term240 A B s x t).
Proof. exact (MK_COMB (@lem4342470 B) (@lem4342469 A B s x t)). Qed.
Lemma lem4342472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342473 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : (term270 A B s x t) = (term257 A B s x t).
Proof. exact (MK_COMB (@lem4342472) (@lem4342471 A B s x t)). Qed.
Lemma lem4342474 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term266 A B s' x t' x') = (term267 A B s' x t' x').
Proof. exact (eq_refl (term266 A B s' x t' x')). Qed.
Lemma lem4342475 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term268 A B s' x t') = (term265 A B s' x t').
Proof. exact (fun_ext (fun x' : B => @lem4342474 A B s' x t' x')). Qed.
Lemma lem4342476 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342477 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term269 A B s' x t') = (term240 A B s' x t').
Proof. exact (MK_COMB (@lem4342476 B) (@lem4342475 A B s' x t')). Qed.
Lemma lem4342478 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term263 A B s t s' x t') = (term259 A B s t s' x t').
Proof. exact (MK_COMB (@lem4342473 A B s x t) (@lem4342477 A B s' x t')). Qed.
Lemma lem4342479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342480 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term271 A B s t s' x t') = (term272 A B s t s' x t').
Proof. exact (MK_COMB (@lem4342479) (@lem4342478 A B s t s' x t')). Qed.
Lemma lem4342481 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term266 A B s x t x') = (term267 A B s x t x').
Proof. exact (eq_refl (term266 A B s x t x')). Qed.
Lemma lem4342482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342483 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) : (term273 A B s x t x') = (term274 A B s x t x').
Proof. exact (MK_COMB (@lem4342482) (@lem4342481 A B s x t x')). Qed.
Lemma lem4342484 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term266 A B s' x t' x') = (term267 A B s' x t' x').
Proof. exact (eq_refl (term266 A B s' x t' x')). Qed.
Lemma lem4342485 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term275 A B s t s' x t' x') = (term276 A B s t s' x t' x').
Proof. exact (MK_COMB (@lem4342483 A B s x t x') (@lem4342484 A B s' x t' x')). Qed.
Lemma lem4342486 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term277 A B s t s' x t') = (term278 A B s t s' x t').
Proof. exact (fun_ext (fun x' : B => @lem4342485 A B s t s' x t' x')). Qed.
Lemma lem4342487 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342488 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term264 A B s t s' x t') = (term279 A B s t s' x t').
Proof. exact (MK_COMB (@lem4342487 B) (@lem4342486 A B s t s' x t')). Qed.
Lemma lem4342489 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : ((term263 A B s t s' x t') = (term264 A B s t s' x t')) = ((term259 A B s t s' x t') = (term279 A B s t s' x t')).
Proof. exact (MK_COMB (@lem4342480 A B s t s' x t') (@lem4342488 A B s t s' x t')). Qed.
Lemma lem4342490 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term259 A B s t s' x t') = (term279 A B s t s' x t').
Proof. exact (EQ_MP (@lem4342489 A B s t s' x t') (@lem4342467 A B s t s' x t')). Qed.
Lemma lem4342491 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term261 A B s t s' t') = (term280 A B s t s' t').
Proof. exact (fun_ext (fun x : A => @lem4342490 A B s t s' x t')). Qed.
Lemma lem4342492 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342493 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term262 A B s t s' t') = (term281 A B s t s' t').
Proof. exact (MK_COMB (@lem4342492 A) (@lem4342491 A B s t s' t')). Qed.
Lemma lem4342494 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term245 A B s t s' t') = (term281 A B s t s' t').
Proof. exact (TRANS (@lem4342463 A B s t s' t') (@lem4342493 A B s t s' t')). Qed.
Lemma lem4342495 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term203 A B s t s' t') = (term281 A B s t s' t').
Proof. exact (TRANS (@lem4342436 A B s t s' t') (@lem4342494 A B s t s' t')). Qed.
Lemma lem4342496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4342497 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term217 A B s t s' t') = (term282 A B s t s' t').
Proof. exact (MK_COMB (@lem4342496) (@lem4342495 A B s t s' t')). Qed.
Lemma lem4342499 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4342500 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (@lem4342499 A P Q). Qed.
Lemma lem4342501 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term283 A s' s) = (term284 A s' s).
Proof. exact (@lem4342500 A (term169 A s s') (term169 A s' s)). Qed.
Lemma lem4342502 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term285 A s s' x) = (term162 A s s' x).
Proof. exact (eq_refl (term285 A s s' x)). Qed.
Lemma lem4342503 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term286 A s s') = (term169 A s s').
Proof. exact (fun_ext (fun x : A => @lem4342502 A s s' x)). Qed.
Lemma lem4342504 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342505 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term287 A s s') = (term170 A s s').
Proof. exact (MK_COMB (@lem4342504 A) (@lem4342503 A s s')). Qed.
Lemma lem4342506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342507 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term288 A s s') = (term174 A s s').
Proof. exact (MK_COMB (@lem4342506) (@lem4342505 A s s')). Qed.
Lemma lem4342508 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term285 A s' s x) = (term162 A s' s x).
Proof. exact (eq_refl (term285 A s' s x)). Qed.
Lemma lem4342509 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term286 A s' s) = (term169 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4342508 A s' s x)). Qed.
Lemma lem4342510 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342511 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term287 A s' s) = (term170 A s' s).
Proof. exact (MK_COMB (@lem4342510 A) (@lem4342509 A s' s)). Qed.
Lemma lem4342512 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term283 A s' s) = (term206 A s' s).
Proof. exact (MK_COMB (@lem4342507 A s s') (@lem4342511 A s' s)). Qed.
Lemma lem4342513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342514 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term289 A s' s) = (term290 A s' s).
Proof. exact (MK_COMB (@lem4342513) (@lem4342512 A s' s)). Qed.
Lemma lem4342515 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term285 A s s' x) = (term162 A s s' x).
Proof. exact (eq_refl (term285 A s s' x)). Qed.
Lemma lem4342516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342517 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term291 A s s' x) = (term292 A s s' x).
Proof. exact (MK_COMB (@lem4342516) (@lem4342515 A s s' x)). Qed.
Lemma lem4342518 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term285 A s' s x) = (term162 A s' s x).
Proof. exact (eq_refl (term285 A s' s x)). Qed.
Lemma lem4342519 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term293 A s' s x) = (term294 A s' s x).
Proof. exact (MK_COMB (@lem4342517 A s s' x) (@lem4342518 A s' s x)). Qed.
Lemma lem4342520 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term295 A s' s) = (term296 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4342519 A s' s x)). Qed.
Lemma lem4342521 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342522 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term284 A s' s) = (term297 A s' s).
Proof. exact (MK_COMB (@lem4342521 A) (@lem4342520 A s' s)). Qed.
Lemma lem4342523 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : ((term283 A s' s) = (term284 A s' s)) = ((term206 A s' s) = (term297 A s' s)).
Proof. exact (MK_COMB (@lem4342514 A s' s) (@lem4342522 A s' s)). Qed.
Lemma lem4342524 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term206 A s' s) = (term297 A s' s).
Proof. exact (EQ_MP (@lem4342523 A s' s) (@lem4342501 A s' s)). Qed.
Lemma lem4342525 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342526 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term210 A s' s) = (term298 A s' s).
Proof. exact (MK_COMB (@lem4342525) (@lem4342524 A s' s)). Qed.
Lemma lem4342528 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4342529 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term246 B P Q) = (term247 B P Q).
Proof. exact (@lem4342528 B P Q). Qed.
Lemma lem4342530 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term283 B t' t) = (term284 B t' t).
Proof. exact (@lem4342529 B (term169 B t t') (term169 B t' t)). Qed.
Lemma lem4342531 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term285 B t t' x) = (term162 B t t' x).
Proof. exact (eq_refl (term285 B t t' x)). Qed.
Lemma lem4342532 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term286 B t t') = (term169 B t t').
Proof. exact (fun_ext (fun x : B => @lem4342531 B t t' x)). Qed.
Lemma lem4342533 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342534 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term287 B t t') = (term170 B t t').
Proof. exact (MK_COMB (@lem4342533 B) (@lem4342532 B t t')). Qed.
Lemma lem4342535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342536 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term288 B t t') = (term174 B t t').
Proof. exact (MK_COMB (@lem4342535) (@lem4342534 B t t')). Qed.
Lemma lem4342537 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term285 B t' t x) = (term162 B t' t x).
Proof. exact (eq_refl (term285 B t' t x)). Qed.
Lemma lem4342538 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term286 B t' t) = (term169 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4342537 B t' t x)). Qed.
Lemma lem4342539 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342540 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term287 B t' t) = (term170 B t' t).
Proof. exact (MK_COMB (@lem4342539 B) (@lem4342538 B t' t)). Qed.
Lemma lem4342541 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term283 B t' t) = (term206 B t' t).
Proof. exact (MK_COMB (@lem4342536 B t t') (@lem4342540 B t' t)). Qed.
Lemma lem4342542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342543 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term289 B t' t) = (term290 B t' t).
Proof. exact (MK_COMB (@lem4342542) (@lem4342541 B t' t)). Qed.
Lemma lem4342544 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term285 B t t' x) = (term162 B t t' x).
Proof. exact (eq_refl (term285 B t t' x)). Qed.
Lemma lem4342545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342546 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term291 B t t' x) = (term292 B t t' x).
Proof. exact (MK_COMB (@lem4342545) (@lem4342544 B t t' x)). Qed.
Lemma lem4342547 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term285 B t' t x) = (term162 B t' t x).
Proof. exact (eq_refl (term285 B t' t x)). Qed.
Lemma lem4342548 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term293 B t' t x) = (term294 B t' t x).
Proof. exact (MK_COMB (@lem4342546 B t t' x) (@lem4342547 B t' t x)). Qed.
Lemma lem4342549 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term295 B t' t) = (term296 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4342548 B t' t x)). Qed.
Lemma lem4342550 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342551 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term284 B t' t) = (term297 B t' t).
Proof. exact (MK_COMB (@lem4342550 B) (@lem4342549 B t' t)). Qed.
Lemma lem4342552 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : ((term283 B t' t) = (term284 B t' t)) = ((term206 B t' t) = (term297 B t' t)).
Proof. exact (MK_COMB (@lem4342543 B t' t) (@lem4342551 B t' t)). Qed.
Lemma lem4342553 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term206 B t' t) = (term297 B t' t).
Proof. exact (EQ_MP (@lem4342552 B t' t) (@lem4342530 B t' t)). Qed.
Lemma lem4342554 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term212 A B s' s t' t) = (term299 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342526 A s' s) (@lem4342553 B t' t)). Qed.
Lemma lem4342558 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4342559 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (@lem4342558 A P Q). Qed.
Lemma lem4342560 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term302 A B s' s t' t) = (term303 A B s' s t' t).
Proof. exact (@lem4342559 A (term296 A s' s) (term297 B t' t)). Qed.
Lemma lem4342561 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term304 A s' s x) = (term294 A s' s x).
Proof. exact (eq_refl (term304 A s' s x)). Qed.
Lemma lem4342562 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term305 A s' s) = (term296 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4342561 A s' s x)). Qed.
Lemma lem4342563 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342564 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term306 A s' s) = (term297 A s' s).
Proof. exact (MK_COMB (@lem4342563 A) (@lem4342562 A s' s)). Qed.
Lemma lem4342565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342566 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term307 A s' s) = (term298 A s' s).
Proof. exact (MK_COMB (@lem4342565) (@lem4342564 A s' s)). Qed.
Lemma lem4342567 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term297 B t' t) = (term297 B t' t).
Proof. exact (eq_refl (term297 B t' t)). Qed.
Lemma lem4342568 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term302 A B s' s t' t) = (term299 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342566 A s' s) (@lem4342567 B t' t)). Qed.
Lemma lem4342569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342570 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term308 A B s' s t' t) = (term309 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342569) (@lem4342568 A B s' s t' t)). Qed.
Lemma lem4342571 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term304 A s' s x) = (term294 A s' s x).
Proof. exact (eq_refl (term304 A s' s x)). Qed.
Lemma lem4342572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342573 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term310 A s' s x) = (term311 A s' s x).
Proof. exact (MK_COMB (@lem4342572) (@lem4342571 A s' s x)). Qed.
Lemma lem4342574 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term297 B t' t) = (term297 B t' t).
Proof. exact (eq_refl (term297 B t' t)). Qed.
Lemma lem4342575 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term312 A B s' s x t' t) = (term313 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4342573 A s' s x) (@lem4342574 B t' t)). Qed.
Lemma lem4342576 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term314 A B s' s t' t) = (term315 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342575 A B s' s x t' t)). Qed.
Lemma lem4342577 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342578 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term303 A B s' s t' t) = (term316 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342577 A) (@lem4342576 A B s' s t' t)). Qed.
Lemma lem4342579 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term302 A B s' s t' t) = (term303 A B s' s t' t)) = ((term299 A B s' s t' t) = (term316 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4342570 A B s' s t' t) (@lem4342578 A B s' s t' t)). Qed.
Lemma lem4342580 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term299 A B s' s t' t) = (term316 A B s' s t' t).
Proof. exact (EQ_MP (@lem4342579 A B s' s t' t) (@lem4342560 A B s' s t' t)). Qed.
Lemma lem4342582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4342583 {B : Type'} (P : Prop) (Q : B -> Prop) : (term317 B P Q) = (term318 B P Q).
Proof. exact (@lem4342582 B P Q). Qed.
Lemma lem4342584 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term319 A B s' s x t' t) = (term320 A B s' s x t' t).
Proof. exact (@lem4342583 B (term294 A s' s x) (term296 B t' t)). Qed.
Lemma lem4342585 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term304 B t' t x) = (term294 B t' t x).
Proof. exact (eq_refl (term304 B t' t x)). Qed.
Lemma lem4342586 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term305 B t' t) = (term296 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4342585 B t' t x)). Qed.
Lemma lem4342587 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342588 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term306 B t' t) = (term297 B t' t).
Proof. exact (MK_COMB (@lem4342587 B) (@lem4342586 B t' t)). Qed.
Lemma lem4342589 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term311 A s' s x) = (term311 A s' s x).
Proof. exact (eq_refl (term311 A s' s x)). Qed.
Lemma lem4342590 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term319 A B s' s x t' t) = (term313 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4342589 A s' s x) (@lem4342588 B t' t)). Qed.
Lemma lem4342591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342592 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term321 A B s' s x t' t) = (term322 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4342591) (@lem4342590 A B s' s x t' t)). Qed.
Lemma lem4342593 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term304 B t' t x) = (term294 B t' t x).
Proof. exact (eq_refl (term304 B t' t x)). Qed.
Lemma lem4342594 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term311 A s' s x) = (term311 A s' s x).
Proof. exact (eq_refl (term311 A s' s x)). Qed.
Lemma lem4342595 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) (x' : B) : (term323 A B s' s x t' t x') = (term324 A B s' s x t' t x').
Proof. exact (MK_COMB (@lem4342594 A s' s x) (@lem4342593 B t' t x')). Qed.
Lemma lem4342596 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term325 A B s' s x t' t) = (term326 A B s' s x t' t).
Proof. exact (fun_ext (fun x' : B => @lem4342595 A B s' s x t' t x')). Qed.
Lemma lem4342597 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342598 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term320 A B s' s x t' t) = (term327 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4342597 B) (@lem4342596 A B s' s x t' t)). Qed.
Lemma lem4342599 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : ((term319 A B s' s x t' t) = (term320 A B s' s x t' t)) = ((term313 A B s' s x t' t) = (term327 A B s' s x t' t)).
Proof. exact (MK_COMB (@lem4342592 A B s' s x t' t) (@lem4342598 A B s' s x t' t)). Qed.
Lemma lem4342600 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term313 A B s' s x t' t) = (term327 A B s' s x t' t).
Proof. exact (EQ_MP (@lem4342599 A B s' s x t' t) (@lem4342584 A B s' s x t' t)). Qed.
Lemma lem4342601 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term315 A B s' s t' t) = (term328 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342600 A B s' s x t' t)). Qed.
Lemma lem4342602 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342603 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term316 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342602 A) (@lem4342601 A B s' s t' t)). Qed.
Lemma lem4342604 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term299 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (TRANS (@lem4342580 A B s' s t' t) (@lem4342603 A B s' s t' t)). Qed.
Lemma lem4342605 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term212 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (TRANS (@lem4342554 A B s' s t' t) (@lem4342604 A B s' s t' t)). Qed.
Lemma lem4342606 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term219 A B s' s t' t) = (term330 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342497 A B s t s' t') (@lem4342605 A B s' s t' t)). Qed.
Lemma lem4342608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4342609 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4342608 A P Q). Qed.
Lemma lem4342610 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term331 A B s' s t' t) = (term332 A B s' s t' t).
Proof. exact (@lem4342609 A (term280 A B s t s' t') (term329 A B s' s t' t)). Qed.
Lemma lem4342611 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term333 A B s t s' t' x) = (term279 A B s t s' x t').
Proof. exact (eq_refl (term333 A B s t s' t' x)). Qed.
Lemma lem4342612 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term334 A B s t s' t') = (term280 A B s t s' t').
Proof. exact (fun_ext (fun x : A => @lem4342611 A B s t s' x t')). Qed.
Lemma lem4342613 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342614 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term335 A B s t s' t') = (term281 A B s t s' t').
Proof. exact (MK_COMB (@lem4342613 A) (@lem4342612 A B s t s' t')). Qed.
Lemma lem4342615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4342616 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term336 A B s t s' t') = (term282 A B s t s' t').
Proof. exact (MK_COMB (@lem4342615) (@lem4342614 A B s t s' t')). Qed.
Lemma lem4342617 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term329 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (eq_refl (term329 A B s' s t' t)). Qed.
Lemma lem4342618 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term331 A B s' s t' t) = (term330 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342616 A B s t s' t') (@lem4342617 A B s' s t' t)). Qed.
Lemma lem4342619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342620 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term337 A B s' s t' t) = (term338 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342619) (@lem4342618 A B s' s t' t)). Qed.
Lemma lem4342621 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term333 A B s t s' t' x) = (term279 A B s t s' x t').
Proof. exact (eq_refl (term333 A B s t s' t' x)). Qed.
Lemma lem4342622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4342623 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term339 A B s t s' t' x) = (term340 A B s t s' x t').
Proof. exact (MK_COMB (@lem4342622) (@lem4342621 A B s t s' x t')). Qed.
Lemma lem4342624 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term329 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (eq_refl (term329 A B s' s t' t)). Qed.
Lemma lem4342625 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term341 A B x s' s t' t) = (term342 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342623 A B s t s' x t') (@lem4342624 A B s' s t' t)). Qed.
Lemma lem4342626 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term343 A B s' s t' t) = (term344 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342625 A B x s' s t' t)). Qed.
Lemma lem4342627 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342628 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term332 A B s' s t' t) = (term345 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342627 A) (@lem4342626 A B s' s t' t)). Qed.
Lemma lem4342629 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term331 A B s' s t' t) = (term332 A B s' s t' t)) = ((term330 A B s' s t' t) = (term345 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4342620 A B s' s t' t) (@lem4342628 A B s' s t' t)). Qed.
Lemma lem4342630 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term330 A B s' s t' t) = (term345 A B s' s t' t).
Proof. exact (EQ_MP (@lem4342629 A B s' s t' t) (@lem4342610 A B s' s t' t)). Qed.
Lemma lem4342632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4342633 {B : Type'} (P : B -> Prop) (Q : Prop) : (term234 B P Q) = (term235 B P Q).
Proof. exact (@lem4342632 B P Q). Qed.
Lemma lem4342634 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term346 A B x s' s t' t) = (term347 A B x s' s t' t).
Proof. exact (@lem4342633 B (term278 A B s t s' x t') (term329 A B s' s t' t)). Qed.
Lemma lem4342635 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term348 A B s t s' x t' x') = (term276 A B s t s' x t' x').
Proof. exact (eq_refl (term348 A B s t s' x t' x')). Qed.
Lemma lem4342636 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term349 A B s t s' x t') = (term278 A B s t s' x t').
Proof. exact (fun_ext (fun x' : B => @lem4342635 A B s t s' x t' x')). Qed.
Lemma lem4342637 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342638 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term350 A B s t s' x t') = (term279 A B s t s' x t').
Proof. exact (MK_COMB (@lem4342637 B) (@lem4342636 A B s t s' x t')). Qed.
Lemma lem4342639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4342640 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) : (term351 A B s t s' x t') = (term340 A B s t s' x t').
Proof. exact (MK_COMB (@lem4342639) (@lem4342638 A B s t s' x t')). Qed.
Lemma lem4342641 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term329 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (eq_refl (term329 A B s' s t' t)). Qed.
Lemma lem4342642 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term346 A B x s' s t' t) = (term342 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342640 A B s t s' x t') (@lem4342641 A B s' s t' t)). Qed.
Lemma lem4342643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342644 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term352 A B x s' s t' t) = (term353 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342643) (@lem4342642 A B x s' s t' t)). Qed.
Lemma lem4342645 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term348 A B s t s' x t' x') = (term276 A B s t s' x t' x').
Proof. exact (eq_refl (term348 A B s t s' x t' x')). Qed.
Lemma lem4342646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4342647 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term354 A B s t s' x t' x') = (term355 A B s t s' x t' x').
Proof. exact (MK_COMB (@lem4342646) (@lem4342645 A B s t s' x t' x')). Qed.
Lemma lem4342648 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term329 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (eq_refl (term329 A B s' s t' t)). Qed.
Lemma lem4342649 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term356 A B x x' s' s t' t) = (term357 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342647 A B s t s' x t' x') (@lem4342648 A B s' s t' t)). Qed.
Lemma lem4342650 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term358 A B x s' s t' t) = (term359 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4342649 A B x x' s' s t' t)). Qed.
Lemma lem4342651 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342652 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term347 A B x s' s t' t) = (term360 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342651 B) (@lem4342650 A B x s' s t' t)). Qed.
Lemma lem4342653 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term346 A B x s' s t' t) = (term347 A B x s' s t' t)) = ((term342 A B x s' s t' t) = (term360 A B x s' s t' t)).
Proof. exact (MK_COMB (@lem4342644 A B x s' s t' t) (@lem4342652 A B x s' s t' t)). Qed.
Lemma lem4342654 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term342 A B x s' s t' t) = (term360 A B x s' s t' t).
Proof. exact (EQ_MP (@lem4342653 A B x s' s t' t) (@lem4342634 A B x s' s t' t)). Qed.
Lemma lem4342656 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342657 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem4342656 A P Q). Qed.
Lemma lem4342658 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term361 A B x x' s' s t' t) = (term362 A B x x' s' s t' t).
Proof. exact (@lem4342657 A (term276 A B s t s' x t' x') (term328 A B s' s t' t)). Qed.
Lemma lem4342659 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term363 A B s' s t' t x) = (term327 A B s' s x t' t).
Proof. exact (eq_refl (term363 A B s' s t' t x)). Qed.
Lemma lem4342660 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term364 A B s' s t' t) = (term328 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342659 A B s' s x t' t)). Qed.
Lemma lem4342661 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342662 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term365 A B s' s t' t) = (term329 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342661 A) (@lem4342660 A B s' s t' t)). Qed.
Lemma lem4342663 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term355 A B s t s' x t' x') = (term355 A B s t s' x t' x').
Proof. exact (eq_refl (term355 A B s t s' x t' x')). Qed.
Lemma lem4342664 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term361 A B x x' s' s t' t) = (term357 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342663 A B s t s' x t' x') (@lem4342662 A B s' s t' t)). Qed.
Lemma lem4342665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342666 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term366 A B x x' s' s t' t) = (term367 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342665) (@lem4342664 A B x x' s' s t' t)). Qed.
Lemma lem4342667 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term363 A B s' s t' t x') = (term327 A B s' s x' t' t).
Proof. exact (eq_refl (term363 A B s' s t' t x')). Qed.
Lemma lem4342668 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term355 A B s t s' x t' x') = (term355 A B s t s' x t' x').
Proof. exact (eq_refl (term355 A B s t s' x t' x')). Qed.
Lemma lem4342669 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term368 A B x x' s' s t' t x'') = (term369 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342668 A B s t s' x t' x') (@lem4342667 A B s' s x'' t' t)). Qed.
Lemma lem4342670 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term370 A B x x' s' s t' t) = (term371 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4342669 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342671 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342672 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term362 A B x x' s' s t' t) = (term372 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342671 A) (@lem4342670 A B x x' s' s t' t)). Qed.
Lemma lem4342673 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term361 A B x x' s' s t' t) = (term362 A B x x' s' s t' t)) = ((term357 A B x x' s' s t' t) = (term372 A B x x' s' s t' t)).
Proof. exact (MK_COMB (@lem4342666 A B x x' s' s t' t) (@lem4342672 A B x x' s' s t' t)). Qed.
Lemma lem4342674 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term357 A B x x' s' s t' t) = (term372 A B x x' s' s t' t).
Proof. exact (EQ_MP (@lem4342673 A B x x' s' s t' t) (@lem4342658 A B x x' s' s t' t)). Qed.
Lemma lem4342676 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342677 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342676 B P Q). Qed.
Lemma lem4342678 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term373 A B x x' s' s x'' t' t) = (term374 A B x x' s' s x'' t' t).
Proof. exact (@lem4342677 B (term276 A B s t s' x t' x') (term326 A B s' s x'' t' t)). Qed.
Lemma lem4342679 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) (x : B) : (term375 A B s' s x' t' t x) = (term324 A B s' s x' t' t x).
Proof. exact (eq_refl (term375 A B s' s x' t' t x)). Qed.
Lemma lem4342680 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term376 A B s' s x' t' t) = (term326 A B s' s x' t' t).
Proof. exact (fun_ext (fun x : B => @lem4342679 A B s' s x' t' t x)). Qed.
Lemma lem4342681 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342682 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term377 A B s' s x' t' t) = (term327 A B s' s x' t' t).
Proof. exact (MK_COMB (@lem4342681 B) (@lem4342680 A B s' s x' t' t)). Qed.
Lemma lem4342683 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term355 A B s t s' x t' x') = (term355 A B s t s' x t' x').
Proof. exact (eq_refl (term355 A B s t s' x t' x')). Qed.
Lemma lem4342684 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term373 A B x x' s' s x'' t' t) = (term369 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342683 A B s t s' x t' x') (@lem4342682 A B s' s x'' t' t)). Qed.
Lemma lem4342685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342686 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term378 A B x x' s' s x'' t' t) = (term379 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342685) (@lem4342684 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342687 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) (x'' : B) : (term375 A B s' s x' t' t x'') = (term324 A B s' s x' t' t x'').
Proof. exact (eq_refl (term375 A B s' s x' t' t x'')). Qed.
Lemma lem4342688 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) : (term355 A B s t s' x t' x') = (term355 A B s t s' x t' x').
Proof. exact (eq_refl (term355 A B s t s' x t' x')). Qed.
Lemma lem4342689 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term380 A B x x' s' s x'' t' t x''') = (term381 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4342688 A B s t s' x t' x') (@lem4342687 A B s' s x'' t' t x''')). Qed.
Lemma lem4342690 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term382 A B x x' s' s x'' t' t) = (term383 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4342689 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4342691 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342692 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term374 A B x x' s' s x'' t' t) = (term384 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342691 B) (@lem4342690 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342693 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : ((term373 A B x x' s' s x'' t' t) = (term374 A B x x' s' s x'' t' t)) = ((term369 A B x x' s' s x'' t' t) = (term384 A B x x' s' s x'' t' t)).
Proof. exact (MK_COMB (@lem4342686 A B x x' s' s x'' t' t) (@lem4342692 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342694 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term369 A B x x' s' s x'' t' t) = (term384 A B x x' s' s x'' t' t).
Proof. exact (EQ_MP (@lem4342693 A B x x' s' s x'' t' t) (@lem4342678 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342695 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term371 A B x x' s' s t' t) = (term385 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4342694 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342696 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342697 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term372 A B x x' s' s t' t) = (term386 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342696 A) (@lem4342695 A B x x' s' s t' t)). Qed.
Lemma lem4342698 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term357 A B x x' s' s t' t) = (term386 A B x x' s' s t' t).
Proof. exact (TRANS (@lem4342674 A B x x' s' s t' t) (@lem4342697 A B x x' s' s t' t)). Qed.
Lemma lem4342699 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term359 A B x s' s t' t) = (term387 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4342698 A B x x' s' s t' t)). Qed.
Lemma lem4342700 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342701 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term360 A B x s' s t' t) = (term388 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342700 B) (@lem4342699 A B x s' s t' t)). Qed.
Lemma lem4342702 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term342 A B x s' s t' t) = (term388 A B x s' s t' t).
Proof. exact (TRANS (@lem4342654 A B x s' s t' t) (@lem4342701 A B x s' s t' t)). Qed.
Lemma lem4342703 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term344 A B s' s t' t) = (term389 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342702 A B x s' s t' t)). Qed.
Lemma lem4342704 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342705 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term345 A B s' s t' t) = (term390 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342704 A) (@lem4342703 A B s' s t' t)). Qed.
Lemma lem4342706 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term330 A B s' s t' t) = (term390 A B s' s t' t).
Proof. exact (TRANS (@lem4342630 A B s' s t' t) (@lem4342705 A B s' s t' t)). Qed.
Lemma lem4342707 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term219 A B s' s t' t) = (term390 A B s' s t' t).
Proof. exact (TRANS (@lem4342606 A B s' s t' t) (@lem4342706 A B s' s t' t)). Qed.
Lemma lem4342708 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342709 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term229 A B s' s t' t) = (term391 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342708 A B s' s t' t) (@lem4342707 A B s' s t' t)). Qed.
Lemma lem4342711 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342712 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem4342711 A P Q). Qed.
Lemma lem4342713 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term392 A B s' s t' t) = (term393 A B s' s t' t).
Proof. exact (@lem4342712 A (term196 A B s' s t' t) (term389 A B s' s t' t)). Qed.
Lemma lem4342714 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term394 A B s' s t' t x) = (term388 A B x s' s t' t).
Proof. exact (eq_refl (term394 A B s' s t' t x)). Qed.
Lemma lem4342715 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term395 A B s' s t' t) = (term389 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342714 A B x s' s t' t)). Qed.
Lemma lem4342716 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342717 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term396 A B s' s t' t) = (term390 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342716 A) (@lem4342715 A B s' s t' t)). Qed.
Lemma lem4342718 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342719 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term392 A B s' s t' t) = (term391 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342718 A B s' s t' t) (@lem4342717 A B s' s t' t)). Qed.
Lemma lem4342720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342721 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term397 A B s' s t' t) = (term398 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342720) (@lem4342719 A B s' s t' t)). Qed.
Lemma lem4342722 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term394 A B s' s t' t x) = (term388 A B x s' s t' t).
Proof. exact (eq_refl (term394 A B s' s t' t x)). Qed.
Lemma lem4342723 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342724 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term399 A B s' s t' t x) = (term400 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342723 A B s' s t' t) (@lem4342722 A B x s' s t' t)). Qed.
Lemma lem4342725 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term401 A B s' s t' t) = (term402 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342724 A B x s' s t' t)). Qed.
Lemma lem4342726 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342727 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term393 A B s' s t' t) = (term403 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342726 A) (@lem4342725 A B s' s t' t)). Qed.
Lemma lem4342728 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term392 A B s' s t' t) = (term393 A B s' s t' t)) = ((term391 A B s' s t' t) = (term403 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4342721 A B s' s t' t) (@lem4342727 A B s' s t' t)). Qed.
Lemma lem4342729 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term391 A B s' s t' t) = (term403 A B s' s t' t).
Proof. exact (EQ_MP (@lem4342728 A B s' s t' t) (@lem4342713 A B s' s t' t)). Qed.
Lemma lem4342731 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342732 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342731 B P Q). Qed.
Lemma lem4342733 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term404 A B x s' s t' t) = (term405 A B x s' s t' t).
Proof. exact (@lem4342732 B (term196 A B s' s t' t) (term387 A B x s' s t' t)). Qed.
Lemma lem4342734 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term406 A B x s' s t' t x') = (term386 A B x x' s' s t' t).
Proof. exact (eq_refl (term406 A B x s' s t' t x')). Qed.
Lemma lem4342735 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term407 A B x s' s t' t) = (term387 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4342734 A B x x' s' s t' t)). Qed.
Lemma lem4342736 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342737 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term408 A B x s' s t' t) = (term388 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342736 B) (@lem4342735 A B x s' s t' t)). Qed.
Lemma lem4342738 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342739 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term404 A B x s' s t' t) = (term400 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342738 A B s' s t' t) (@lem4342737 A B x s' s t' t)). Qed.
Lemma lem4342740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342741 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term409 A B x s' s t' t) = (term410 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342740) (@lem4342739 A B x s' s t' t)). Qed.
Lemma lem4342742 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term406 A B x s' s t' t x') = (term386 A B x x' s' s t' t).
Proof. exact (eq_refl (term406 A B x s' s t' t x')). Qed.
Lemma lem4342743 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342744 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term411 A B x s' s t' t x') = (term412 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342743 A B s' s t' t) (@lem4342742 A B x x' s' s t' t)). Qed.
Lemma lem4342745 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term413 A B x s' s t' t) = (term414 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4342744 A B x x' s' s t' t)). Qed.
Lemma lem4342746 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342747 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term405 A B x s' s t' t) = (term415 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342746 B) (@lem4342745 A B x s' s t' t)). Qed.
Lemma lem4342748 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term404 A B x s' s t' t) = (term405 A B x s' s t' t)) = ((term400 A B x s' s t' t) = (term415 A B x s' s t' t)).
Proof. exact (MK_COMB (@lem4342741 A B x s' s t' t) (@lem4342747 A B x s' s t' t)). Qed.
Lemma lem4342749 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term400 A B x s' s t' t) = (term415 A B x s' s t' t).
Proof. exact (EQ_MP (@lem4342748 A B x s' s t' t) (@lem4342733 A B x s' s t' t)). Qed.
Lemma lem4342751 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342752 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem4342751 A P Q). Qed.
Lemma lem4342753 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term416 A B x x' s' s t' t) = (term417 A B x x' s' s t' t).
Proof. exact (@lem4342752 A (term196 A B s' s t' t) (term385 A B x x' s' s t' t)). Qed.
Lemma lem4342754 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term418 A B x x' s' s t' t x'') = (term384 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term418 A B x x' s' s t' t x'')). Qed.
Lemma lem4342755 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term419 A B x x' s' s t' t) = (term385 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4342754 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342756 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342757 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term420 A B x x' s' s t' t) = (term386 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342756 A) (@lem4342755 A B x x' s' s t' t)). Qed.
Lemma lem4342758 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342759 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term416 A B x x' s' s t' t) = (term412 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342758 A B s' s t' t) (@lem4342757 A B x x' s' s t' t)). Qed.
Lemma lem4342760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342761 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term421 A B x x' s' s t' t) = (term422 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342760) (@lem4342759 A B x x' s' s t' t)). Qed.
Lemma lem4342762 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term418 A B x x' s' s t' t x'') = (term384 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term418 A B x x' s' s t' t x'')). Qed.
Lemma lem4342763 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342764 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term423 A B x x' s' s t' t x'') = (term424 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342763 A B s' s t' t) (@lem4342762 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342765 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term425 A B x x' s' s t' t) = (term426 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4342764 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342766 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342767 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term417 A B x x' s' s t' t) = (term427 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342766 A) (@lem4342765 A B x x' s' s t' t)). Qed.
Lemma lem4342768 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term416 A B x x' s' s t' t) = (term417 A B x x' s' s t' t)) = ((term412 A B x x' s' s t' t) = (term427 A B x x' s' s t' t)).
Proof. exact (MK_COMB (@lem4342761 A B x x' s' s t' t) (@lem4342767 A B x x' s' s t' t)). Qed.
Lemma lem4342769 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term412 A B x x' s' s t' t) = (term427 A B x x' s' s t' t).
Proof. exact (EQ_MP (@lem4342768 A B x x' s' s t' t) (@lem4342753 A B x x' s' s t' t)). Qed.
Lemma lem4342771 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342772 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342771 B P Q). Qed.
Lemma lem4342773 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term428 A B x x' s' s x'' t' t) = (term429 A B x x' s' s x'' t' t).
Proof. exact (@lem4342772 B (term196 A B s' s t' t) (term383 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342774 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term430 A B x x' s' s x'' t' t x''') = (term381 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term430 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4342775 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term431 A B x x' s' s x'' t' t) = (term383 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4342774 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4342776 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342777 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term432 A B x x' s' s x'' t' t) = (term384 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342776 B) (@lem4342775 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342778 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342779 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term428 A B x x' s' s x'' t' t) = (term424 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342778 A B s' s t' t) (@lem4342777 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342781 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term433 A B x x' s' s x'' t' t) = (term434 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342780) (@lem4342779 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342782 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term430 A B x x' s' s x'' t' t x''') = (term381 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term430 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4342783 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (eq_refl (term227 A B s' s t' t)). Qed.
Lemma lem4342784 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term435 A B x x' s' s x'' t' t x''') = (term436 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4342783 A B s' s t' t) (@lem4342782 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4342785 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term437 A B x x' s' s x'' t' t) = (term438 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4342784 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4342786 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342787 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term429 A B x x' s' s x'' t' t) = (term439 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4342786 B) (@lem4342785 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342788 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : ((term428 A B x x' s' s x'' t' t) = (term429 A B x x' s' s x'' t' t)) = ((term424 A B x x' s' s x'' t' t) = (term439 A B x x' s' s x'' t' t)).
Proof. exact (MK_COMB (@lem4342781 A B x x' s' s x'' t' t) (@lem4342787 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342789 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term424 A B x x' s' s x'' t' t) = (term439 A B x x' s' s x'' t' t).
Proof. exact (EQ_MP (@lem4342788 A B x x' s' s x'' t' t) (@lem4342773 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342790 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term426 A B x x' s' s t' t) = (term440 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4342789 A B x x' s' s x'' t' t)). Qed.
Lemma lem4342791 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342792 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term427 A B x x' s' s t' t) = (term441 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4342791 A) (@lem4342790 A B x x' s' s t' t)). Qed.
Lemma lem4342793 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term412 A B x x' s' s t' t) = (term441 A B x x' s' s t' t).
Proof. exact (TRANS (@lem4342769 A B x x' s' s t' t) (@lem4342792 A B x x' s' s t' t)). Qed.
Lemma lem4342794 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term414 A B x s' s t' t) = (term442 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4342793 A B x x' s' s t' t)). Qed.
Lemma lem4342795 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342796 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term415 A B x s' s t' t) = (term443 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4342795 B) (@lem4342794 A B x s' s t' t)). Qed.
Lemma lem4342797 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term400 A B x s' s t' t) = (term443 A B x s' s t' t).
Proof. exact (TRANS (@lem4342749 A B x s' s t' t) (@lem4342796 A B x s' s t' t)). Qed.
Lemma lem4342798 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term402 A B s' s t' t) = (term444 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4342797 A B x s' s t' t)). Qed.
Lemma lem4342799 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342800 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term403 A B s' s t' t) = (term445 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342799 A) (@lem4342798 A B s' s t' t)). Qed.
Lemma lem4342801 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term391 A B s' s t' t) = (term445 A B s' s t' t).
Proof. exact (TRANS (@lem4342729 A B s' s t' t) (@lem4342800 A B s' s t' t)). Qed.
Lemma lem4342802 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term229 A B s' s t' t) = (term445 A B s' s t' t).
Proof. exact (TRANS (@lem4342709 A B s' s t' t) (@lem4342801 A B s' s t' t)). Qed.
Lemma lem4342803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342804 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term231 A B s' s t' t) = (term446 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342803) (@lem4342802 A B s' s t' t)). Qed.
Lemma lem4342808 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4342809 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (@lem4342808 A P Q). Qed.
Lemma lem4342810 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term447 A B s s' t t') = (term448 A B s s' t t').
Proof. exact (@lem4342809 A (term169 A s s') (term170 B t t')). Qed.
Lemma lem4342811 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term285 A s s' x) = (term162 A s s' x).
Proof. exact (eq_refl (term285 A s s' x)). Qed.
Lemma lem4342812 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term286 A s s') = (term169 A s s').
Proof. exact (fun_ext (fun x : A => @lem4342811 A s s' x)). Qed.
Lemma lem4342813 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342814 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term287 A s s') = (term170 A s s').
Proof. exact (MK_COMB (@lem4342813 A) (@lem4342812 A s s')). Qed.
Lemma lem4342815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342816 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term288 A s s') = (term174 A s s').
Proof. exact (MK_COMB (@lem4342815) (@lem4342814 A s s')). Qed.
Lemma lem4342817 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term170 B t t') = (term170 B t t').
Proof. exact (eq_refl (term170 B t t')). Qed.
Lemma lem4342818 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term447 A B s s' t t') = (term176 A B s s' t t').
Proof. exact (MK_COMB (@lem4342816 A s s') (@lem4342817 B t t')). Qed.
Lemma lem4342819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342820 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term449 A B s s' t t') = (term450 A B s s' t t').
Proof. exact (MK_COMB (@lem4342819) (@lem4342818 A B s s' t t')). Qed.
Lemma lem4342821 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term285 A s s' x) = (term162 A s s' x).
Proof. exact (eq_refl (term285 A s s' x)). Qed.
Lemma lem4342822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342823 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term291 A s s' x) = (term292 A s s' x).
Proof. exact (MK_COMB (@lem4342822) (@lem4342821 A s s' x)). Qed.
Lemma lem4342824 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term170 B t t') = (term170 B t t').
Proof. exact (eq_refl (term170 B t t')). Qed.
Lemma lem4342825 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term451 A B s s' x t t') = (term452 A B s s' x t t').
Proof. exact (MK_COMB (@lem4342823 A s s' x) (@lem4342824 B t t')). Qed.
Lemma lem4342826 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term453 A B s s' t t') = (term454 A B s s' t t').
Proof. exact (fun_ext (fun x : A => @lem4342825 A B s s' x t t')). Qed.
Lemma lem4342827 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342828 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term448 A B s s' t t') = (term455 A B s s' t t').
Proof. exact (MK_COMB (@lem4342827 A) (@lem4342826 A B s s' t t')). Qed.
Lemma lem4342829 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term447 A B s s' t t') = (term448 A B s s' t t')) = ((term176 A B s s' t t') = (term455 A B s s' t t')).
Proof. exact (MK_COMB (@lem4342820 A B s s' t t') (@lem4342828 A B s s' t t')). Qed.
Lemma lem4342830 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term176 A B s s' t t') = (term455 A B s s' t t').
Proof. exact (EQ_MP (@lem4342829 A B s s' t t') (@lem4342810 A B s s' t t')). Qed.
Lemma lem4342832 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4342833 {B : Type'} (P : Prop) (Q : B -> Prop) : (term317 B P Q) = (term318 B P Q).
Proof. exact (@lem4342832 B P Q). Qed.
Lemma lem4342834 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term456 A B s s' x t t') = (term457 A B s s' x t t').
Proof. exact (@lem4342833 B (term162 A s s' x) (term169 B t t')). Qed.
Lemma lem4342835 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term285 B t t' x) = (term162 B t t' x).
Proof. exact (eq_refl (term285 B t t' x)). Qed.
Lemma lem4342836 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term286 B t t') = (term169 B t t').
Proof. exact (fun_ext (fun x : B => @lem4342835 B t t' x)). Qed.
Lemma lem4342837 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342838 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term287 B t t') = (term170 B t t').
Proof. exact (MK_COMB (@lem4342837 B) (@lem4342836 B t t')). Qed.
Lemma lem4342839 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term292 A s s' x) = (term292 A s s' x).
Proof. exact (eq_refl (term292 A s s' x)). Qed.
Lemma lem4342840 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term456 A B s s' x t t') = (term452 A B s s' x t t').
Proof. exact (MK_COMB (@lem4342839 A s s' x) (@lem4342838 B t t')). Qed.
Lemma lem4342841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342842 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term458 A B s s' x t t') = (term459 A B s s' x t t').
Proof. exact (MK_COMB (@lem4342841) (@lem4342840 A B s s' x t t')). Qed.
Lemma lem4342843 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term285 B t t' x) = (term162 B t t' x).
Proof. exact (eq_refl (term285 B t t' x)). Qed.
Lemma lem4342844 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term292 A s s' x) = (term292 A s s' x).
Proof. exact (eq_refl (term292 A s s' x)). Qed.
Lemma lem4342845 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) (x' : B) : (term460 A B s s' x t t' x') = (term461 A B s s' x t t' x').
Proof. exact (MK_COMB (@lem4342844 A s s' x) (@lem4342843 B t t' x')). Qed.
Lemma lem4342846 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term462 A B s s' x t t') = (term463 A B s s' x t t').
Proof. exact (fun_ext (fun x' : B => @lem4342845 A B s s' x t t' x')). Qed.
Lemma lem4342847 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342848 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term457 A B s s' x t t') = (term464 A B s s' x t t').
Proof. exact (MK_COMB (@lem4342847 B) (@lem4342846 A B s s' x t t')). Qed.
Lemma lem4342849 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : ((term456 A B s s' x t t') = (term457 A B s s' x t t')) = ((term452 A B s s' x t t') = (term464 A B s s' x t t')).
Proof. exact (MK_COMB (@lem4342842 A B s s' x t t') (@lem4342848 A B s s' x t t')). Qed.
Lemma lem4342850 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term452 A B s s' x t t') = (term464 A B s s' x t t').
Proof. exact (EQ_MP (@lem4342849 A B s s' x t t') (@lem4342834 A B s s' x t t')). Qed.
Lemma lem4342851 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term454 A B s s' t t') = (term465 A B s s' t t').
Proof. exact (fun_ext (fun x : A => @lem4342850 A B s s' x t t')). Qed.
Lemma lem4342852 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342853 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term455 A B s s' t t') = (term466 A B s s' t t').
Proof. exact (MK_COMB (@lem4342852 A) (@lem4342851 A B s s' t t')). Qed.
Lemma lem4342854 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term176 A B s s' t t') = (term466 A B s s' t t').
Proof. exact (TRANS (@lem4342830 A B s s' t t') (@lem4342853 A B s s' t t')). Qed.
Lemma lem4342855 {B : Type'} (t : B -> Prop) : (term181 B t) = (term181 B t).
Proof. exact (eq_refl (term181 B t)). Qed.
Lemma lem4342856 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term183 A B s s' t t') = (term467 A B s s' t t').
Proof. exact (MK_COMB (@lem4342855 B t) (@lem4342854 A B s s' t t')). Qed.
Lemma lem4342858 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4342859 {B : Type'} (P : B -> Prop) (Q : Prop) : (term234 B P Q) = (term235 B P Q).
Proof. exact (@lem4342858 B P Q). Qed.
Lemma lem4342860 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term467 A B s s' t t') = (term468 A B s s' t t').
Proof. exact (@lem4342859 B t (term466 A B s s' t t')). Qed.
Lemma lem4342862 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342863 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem4342862 A P Q). Qed.
Lemma lem4342864 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term469 A B x s s' t t') = (term470 A B x s s' t t').
Proof. exact (@lem4342863 A (t x) (term465 A B s s' t t')). Qed.
Lemma lem4342865 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term471 A B s s' t t' x) = (term464 A B s s' x t t').
Proof. exact (eq_refl (term471 A B s s' t t' x)). Qed.
Lemma lem4342866 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term472 A B s s' t t') = (term465 A B s s' t t').
Proof. exact (fun_ext (fun x : A => @lem4342865 A B s s' x t t')). Qed.
Lemma lem4342867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342868 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term473 A B s s' t t') = (term466 A B s s' t t').
Proof. exact (MK_COMB (@lem4342867 A) (@lem4342866 A B s s' t t')). Qed.
Lemma lem4342869 {B : Type'} (t : B -> Prop) (x : B) : (term474 B t x) = (term474 B t x).
Proof. exact (eq_refl (term474 B t x)). Qed.
Lemma lem4342870 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term469 A B x s s' t t') = (term475 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342869 B t x) (@lem4342868 A B s s' t t')). Qed.
Lemma lem4342871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342872 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term476 A B x s s' t t') = (term477 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342871) (@lem4342870 A B x s s' t t')). Qed.
Lemma lem4342873 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term471 A B s s' t t' x) = (term464 A B s s' x t t').
Proof. exact (eq_refl (term471 A B s s' t t' x)). Qed.
Lemma lem4342874 {B : Type'} (t : B -> Prop) (x : B) : (term474 B t x) = (term474 B t x).
Proof. exact (eq_refl (term474 B t x)). Qed.
Lemma lem4342875 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term478 A B x s s' t t' x') = (term479 A B x s s' x' t t').
Proof. exact (MK_COMB (@lem4342874 B t x) (@lem4342873 A B s s' x' t t')). Qed.
Lemma lem4342876 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term480 A B x s s' t t') = (term481 A B x s s' t t').
Proof. exact (fun_ext (fun x' : A => @lem4342875 A B x s s' x' t t')). Qed.
Lemma lem4342877 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342878 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term470 A B x s s' t t') = (term482 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342877 A) (@lem4342876 A B x s s' t t')). Qed.
Lemma lem4342879 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term469 A B x s s' t t') = (term470 A B x s s' t t')) = ((term475 A B x s s' t t') = (term482 A B x s s' t t')).
Proof. exact (MK_COMB (@lem4342872 A B x s s' t t') (@lem4342878 A B x s s' t t')). Qed.
Lemma lem4342880 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term475 A B x s s' t t') = (term482 A B x s s' t t').
Proof. exact (EQ_MP (@lem4342879 A B x s s' t t') (@lem4342864 A B x s s' t t')). Qed.
Lemma lem4342882 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342883 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342882 B P Q). Qed.
Lemma lem4342884 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term483 A B x s s' x' t t') = (term484 A B x s s' x' t t').
Proof. exact (@lem4342883 B (t x) (term463 A B s s' x' t t')). Qed.
Lemma lem4342885 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) (x' : B) : (term485 A B s s' x t t' x') = (term461 A B s s' x t t' x').
Proof. exact (eq_refl (term485 A B s s' x t t' x')). Qed.
Lemma lem4342886 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term486 A B s s' x t t') = (term463 A B s s' x t t').
Proof. exact (fun_ext (fun x' : B => @lem4342885 A B s s' x t t' x')). Qed.
Lemma lem4342887 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342888 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) : (term487 A B s s' x t t') = (term464 A B s s' x t t').
Proof. exact (MK_COMB (@lem4342887 B) (@lem4342886 A B s s' x t t')). Qed.
Lemma lem4342889 {B : Type'} (t : B -> Prop) (x : B) : (term474 B t x) = (term474 B t x).
Proof. exact (eq_refl (term474 B t x)). Qed.
Lemma lem4342890 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term483 A B x s s' x' t t') = (term479 A B x s s' x' t t').
Proof. exact (MK_COMB (@lem4342889 B t x) (@lem4342888 A B s s' x' t t')). Qed.
Lemma lem4342891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342892 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term488 A B x s s' x' t t') = (term489 A B x s s' x' t t').
Proof. exact (MK_COMB (@lem4342891) (@lem4342890 A B x s s' x' t t')). Qed.
Lemma lem4342893 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) (t : B -> Prop) (t' : B -> Prop) (x' : B) : (term485 A B s s' x t t' x') = (term461 A B s s' x t t' x').
Proof. exact (eq_refl (term485 A B s s' x t t' x')). Qed.
Lemma lem4342894 {B : Type'} (t : B -> Prop) (x : B) : (term474 B t x) = (term474 B t x).
Proof. exact (eq_refl (term474 B t x)). Qed.
Lemma lem4342895 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) (x'' : B) : (term490 A B x s s' x' t t' x'') = (term491 A B x s s' x' t t' x'').
Proof. exact (MK_COMB (@lem4342894 B t x) (@lem4342893 A B s s' x' t t' x'')). Qed.
Lemma lem4342896 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term492 A B x s s' x' t t') = (term493 A B x s s' x' t t').
Proof. exact (fun_ext (fun x'' : B => @lem4342895 A B x s s' x' t t' x'')). Qed.
Lemma lem4342897 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342898 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term484 A B x s s' x' t t') = (term494 A B x s s' x' t t').
Proof. exact (MK_COMB (@lem4342897 B) (@lem4342896 A B x s s' x' t t')). Qed.
Lemma lem4342899 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : ((term483 A B x s s' x' t t') = (term484 A B x s s' x' t t')) = ((term479 A B x s s' x' t t') = (term494 A B x s s' x' t t')).
Proof. exact (MK_COMB (@lem4342892 A B x s s' x' t t') (@lem4342898 A B x s s' x' t t')). Qed.
Lemma lem4342900 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term479 A B x s s' x' t t') = (term494 A B x s s' x' t t').
Proof. exact (EQ_MP (@lem4342899 A B x s s' x' t t') (@lem4342884 A B x s s' x' t t')). Qed.
Lemma lem4342901 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term481 A B x s s' t t') = (term495 A B x s s' t t').
Proof. exact (fun_ext (fun x' : A => @lem4342900 A B x s s' x' t t')). Qed.
Lemma lem4342902 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342903 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term482 A B x s s' t t') = (term496 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342902 A) (@lem4342901 A B x s s' t t')). Qed.
Lemma lem4342904 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term475 A B x s s' t t') = (term496 A B x s s' t t').
Proof. exact (TRANS (@lem4342880 A B x s s' t t') (@lem4342903 A B x s s' t t')). Qed.
Lemma lem4342905 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term497 A B s s' t t') = (term498 A B s s' t t').
Proof. exact (fun_ext (fun x : B => @lem4342904 A B x s s' t t')). Qed.
Lemma lem4342906 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342907 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term468 A B s s' t t') = (term499 A B s s' t t').
Proof. exact (MK_COMB (@lem4342906 B) (@lem4342905 A B s s' t t')). Qed.
Lemma lem4342908 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term467 A B s s' t t') = (term499 A B s s' t t').
Proof. exact (TRANS (@lem4342860 A B s s' t t') (@lem4342907 A B s s' t t')). Qed.
Lemma lem4342909 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term183 A B s s' t t') = (term499 A B s s' t t').
Proof. exact (TRANS (@lem4342856 A B s s' t t') (@lem4342908 A B s s' t t')). Qed.
Lemma lem4342910 {A : Type'} (s : A -> Prop) : (term181 A s) = (term181 A s).
Proof. exact (eq_refl (term181 A s)). Qed.
Lemma lem4342911 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term187 A B s s' t t') = (term500 A B s s' t t').
Proof. exact (MK_COMB (@lem4342910 A s) (@lem4342909 A B s s' t t')). Qed.
Lemma lem4342913 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4342914 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4342913 A P Q). Qed.
Lemma lem4342915 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term500 A B s s' t t') = (term501 A B s s' t t').
Proof. exact (@lem4342914 A s (term499 A B s s' t t')). Qed.
Lemma lem4342917 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342918 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342917 B P Q). Qed.
Lemma lem4342919 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term502 A B x s s' t t') = (term503 A B x s s' t t').
Proof. exact (@lem4342918 B (s x) (term498 A B s s' t t')). Qed.
Lemma lem4342920 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term504 A B s s' t t' x) = (term496 A B x s s' t t').
Proof. exact (eq_refl (term504 A B s s' t t' x)). Qed.
Lemma lem4342921 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term505 A B s s' t t') = (term498 A B s s' t t').
Proof. exact (fun_ext (fun x : B => @lem4342920 A B x s s' t t')). Qed.
Lemma lem4342922 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342923 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term506 A B s s' t t') = (term499 A B s s' t t').
Proof. exact (MK_COMB (@lem4342922 B) (@lem4342921 A B s s' t t')). Qed.
Lemma lem4342924 {A : Type'} (s : A -> Prop) (x : A) : (term474 A s x) = (term474 A s x).
Proof. exact (eq_refl (term474 A s x)). Qed.
Lemma lem4342925 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term502 A B x s s' t t') = (term507 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342924 A s x) (@lem4342923 A B s s' t t')). Qed.
Lemma lem4342926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342927 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term508 A B x s s' t t') = (term509 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342926) (@lem4342925 A B x s s' t t')). Qed.
Lemma lem4342928 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term504 A B s s' t t' x) = (term496 A B x s s' t t').
Proof. exact (eq_refl (term504 A B s s' t t' x)). Qed.
Lemma lem4342929 {A : Type'} (s : A -> Prop) (x : A) : (term474 A s x) = (term474 A s x).
Proof. exact (eq_refl (term474 A s x)). Qed.
Lemma lem4342930 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term510 A B x s s' t t' x') = (term511 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4342929 A s x) (@lem4342928 A B x' s s' t t')). Qed.
Lemma lem4342931 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term512 A B x s s' t t') = (term513 A B x s s' t t').
Proof. exact (fun_ext (fun x' : B => @lem4342930 A B x x' s s' t t')). Qed.
Lemma lem4342932 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342933 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term503 A B x s s' t t') = (term514 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342932 B) (@lem4342931 A B x s s' t t')). Qed.
Lemma lem4342934 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term502 A B x s s' t t') = (term503 A B x s s' t t')) = ((term507 A B x s s' t t') = (term514 A B x s s' t t')).
Proof. exact (MK_COMB (@lem4342927 A B x s s' t t') (@lem4342933 A B x s s' t t')). Qed.
Lemma lem4342935 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term507 A B x s s' t t') = (term514 A B x s s' t t').
Proof. exact (EQ_MP (@lem4342934 A B x s s' t t') (@lem4342919 A B x s s' t t')). Qed.
Lemma lem4342937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem4342937 A P Q). Qed.
Lemma lem4342939 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term515 A B x x' s s' t t') = (term516 A B x x' s s' t t').
Proof. exact (@lem4342938 A (s x) (term495 A B x' s s' t t')). Qed.
Lemma lem4342940 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term517 A B x s s' t t' x') = (term494 A B x s s' x' t t').
Proof. exact (eq_refl (term517 A B x s s' t t' x')). Qed.
Lemma lem4342941 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term518 A B x s s' t t') = (term495 A B x s s' t t').
Proof. exact (fun_ext (fun x' : A => @lem4342940 A B x s s' x' t t')). Qed.
Lemma lem4342942 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342943 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term519 A B x s s' t t') = (term496 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342942 A) (@lem4342941 A B x s s' t t')). Qed.
Lemma lem4342944 {A : Type'} (s : A -> Prop) (x : A) : (term474 A s x) = (term474 A s x).
Proof. exact (eq_refl (term474 A s x)). Qed.
Lemma lem4342945 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term515 A B x x' s s' t t') = (term511 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4342944 A s x) (@lem4342943 A B x' s s' t t')). Qed.
Lemma lem4342946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342947 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term520 A B x x' s s' t t') = (term521 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4342946) (@lem4342945 A B x x' s s' t t')). Qed.
Lemma lem4342948 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term517 A B x s s' t t' x') = (term494 A B x s s' x' t t').
Proof. exact (eq_refl (term517 A B x s s' t t' x')). Qed.
Lemma lem4342949 {A : Type'} (s : A -> Prop) (x : A) : (term474 A s x) = (term474 A s x).
Proof. exact (eq_refl (term474 A s x)). Qed.
Lemma lem4342950 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term522 A B x x' s s' t t' x'') = (term523 A B x x' s s' x'' t t').
Proof. exact (MK_COMB (@lem4342949 A s x) (@lem4342948 A B x' s s' x'' t t')). Qed.
Lemma lem4342951 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term524 A B x x' s s' t t') = (term525 A B x x' s s' t t').
Proof. exact (fun_ext (fun x'' : A => @lem4342950 A B x x' s s' x'' t t')). Qed.
Lemma lem4342952 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342953 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term516 A B x x' s s' t t') = (term526 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4342952 A) (@lem4342951 A B x x' s s' t t')). Qed.
Lemma lem4342954 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : ((term515 A B x x' s s' t t') = (term516 A B x x' s s' t t')) = ((term511 A B x x' s s' t t') = (term526 A B x x' s s' t t')).
Proof. exact (MK_COMB (@lem4342947 A B x x' s s' t t') (@lem4342953 A B x x' s s' t t')). Qed.
Lemma lem4342955 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term511 A B x x' s s' t t') = (term526 A B x x' s s' t t').
Proof. exact (EQ_MP (@lem4342954 A B x x' s s' t t') (@lem4342939 A B x x' s s' t t')). Qed.
Lemma lem4342957 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4342958 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4342957 B P Q). Qed.
Lemma lem4342959 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term527 A B x x' s s' x'' t t') = (term528 A B x x' s s' x'' t t').
Proof. exact (@lem4342958 B (s x) (term493 A B x' s s' x'' t t')). Qed.
Lemma lem4342960 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) (x'' : B) : (term529 A B x s s' x' t t' x'') = (term491 A B x s s' x' t t' x'').
Proof. exact (eq_refl (term529 A B x s s' x' t t' x'')). Qed.
Lemma lem4342961 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term530 A B x s s' x' t t') = (term493 A B x s s' x' t t').
Proof. exact (fun_ext (fun x'' : B => @lem4342960 A B x s s' x' t t' x'')). Qed.
Lemma lem4342962 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342963 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) : (term531 A B x s s' x' t t') = (term494 A B x s s' x' t t').
Proof. exact (MK_COMB (@lem4342962 B) (@lem4342961 A B x s s' x' t t')). Qed.
Lemma lem4342964 {A : Type'} (s : A -> Prop) (x : A) : (term474 A s x) = (term474 A s x).
Proof. exact (eq_refl (term474 A s x)). Qed.
Lemma lem4342965 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term527 A B x x' s s' x'' t t') = (term523 A B x x' s s' x'' t t').
Proof. exact (MK_COMB (@lem4342964 A s x) (@lem4342963 A B x' s s' x'' t t')). Qed.
Lemma lem4342966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4342967 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term532 A B x x' s s' x'' t t') = (term533 A B x x' s s' x'' t t').
Proof. exact (MK_COMB (@lem4342966) (@lem4342965 A B x x' s s' x'' t t')). Qed.
Lemma lem4342968 {A B : Type'} (x : B) (s : A -> Prop) (s' : A -> Prop) (x' : A) (t : B -> Prop) (t' : B -> Prop) (x'' : B) : (term529 A B x s s' x' t t' x'') = (term491 A B x s s' x' t t' x'').
Proof. exact (eq_refl (term529 A B x s s' x' t t' x'')). Qed.
Lemma lem4342969 {A : Type'} (s : A -> Prop) (x : A) : (term474 A s x) = (term474 A s x).
Proof. exact (eq_refl (term474 A s x)). Qed.
Lemma lem4342970 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) : (term534 A B x x' s s' x'' t t' x''') = (term535 A B x x' s s' x'' t t' x''').
Proof. exact (MK_COMB (@lem4342969 A s x) (@lem4342968 A B x' s s' x'' t t' x''')). Qed.
Lemma lem4342971 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term536 A B x x' s s' x'' t t') = (term537 A B x x' s s' x'' t t').
Proof. exact (fun_ext (fun x''' : B => @lem4342970 A B x x' s s' x'' t t' x''')). Qed.
Lemma lem4342972 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342973 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term528 A B x x' s s' x'' t t') = (term538 A B x x' s s' x'' t t').
Proof. exact (MK_COMB (@lem4342972 B) (@lem4342971 A B x x' s s' x'' t t')). Qed.
Lemma lem4342974 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : ((term527 A B x x' s s' x'' t t') = (term528 A B x x' s s' x'' t t')) = ((term523 A B x x' s s' x'' t t') = (term538 A B x x' s s' x'' t t')).
Proof. exact (MK_COMB (@lem4342967 A B x x' s s' x'' t t') (@lem4342973 A B x x' s s' x'' t t')). Qed.
Lemma lem4342975 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term523 A B x x' s s' x'' t t') = (term538 A B x x' s s' x'' t t').
Proof. exact (EQ_MP (@lem4342974 A B x x' s s' x'' t t') (@lem4342959 A B x x' s s' x'' t t')). Qed.
Lemma lem4342976 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term525 A B x x' s s' t t') = (term539 A B x x' s s' t t').
Proof. exact (fun_ext (fun x'' : A => @lem4342975 A B x x' s s' x'' t t')). Qed.
Lemma lem4342977 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342978 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term526 A B x x' s s' t t') = (term540 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4342977 A) (@lem4342976 A B x x' s s' t t')). Qed.
Lemma lem4342979 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term511 A B x x' s s' t t') = (term540 A B x x' s s' t t').
Proof. exact (TRANS (@lem4342955 A B x x' s s' t t') (@lem4342978 A B x x' s s' t t')). Qed.
Lemma lem4342980 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term513 A B x s s' t t') = (term541 A B x s s' t t').
Proof. exact (fun_ext (fun x' : B => @lem4342979 A B x x' s s' t t')). Qed.
Lemma lem4342981 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4342982 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term514 A B x s s' t t') = (term542 A B x s s' t t').
Proof. exact (MK_COMB (@lem4342981 B) (@lem4342980 A B x s s' t t')). Qed.
Lemma lem4342983 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term507 A B x s s' t t') = (term542 A B x s s' t t').
Proof. exact (TRANS (@lem4342935 A B x s s' t t') (@lem4342982 A B x s s' t t')). Qed.
Lemma lem4342984 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term543 A B s s' t t') = (term544 A B s s' t t').
Proof. exact (fun_ext (fun x : A => @lem4342983 A B x s s' t t')). Qed.
Lemma lem4342985 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4342986 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term501 A B s s' t t') = (term545 A B s s' t t').
Proof. exact (MK_COMB (@lem4342985 A) (@lem4342984 A B s s' t t')). Qed.
Lemma lem4342987 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term500 A B s s' t t') = (term545 A B s s' t t').
Proof. exact (TRANS (@lem4342915 A B s s' t t') (@lem4342986 A B s s' t t')). Qed.
Lemma lem4342988 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term187 A B s s' t t') = (term545 A B s s' t t').
Proof. exact (TRANS (@lem4342911 A B s s' t t') (@lem4342987 A B s s' t t')). Qed.
Lemma lem4342989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4342990 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term191 A B s s' t t') = (term546 A B s s' t t').
Proof. exact (MK_COMB (@lem4342989) (@lem4342988 A B s s' t t')). Qed.
Lemma lem4342994 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4342995 {A : Type'} (P : A -> Prop) (Q : Prop) : (term300 A P Q) = (term301 A P Q).
Proof. exact (@lem4342994 A P Q). Qed.
Lemma lem4342996 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term447 A B s' s t' t) = (term448 A B s' s t' t).
Proof. exact (@lem4342995 A (term169 A s' s) (term170 B t' t)). Qed.
Lemma lem4342997 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term285 A s' s x) = (term162 A s' s x).
Proof. exact (eq_refl (term285 A s' s x)). Qed.
Lemma lem4342998 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term286 A s' s) = (term169 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4342997 A s' s x)). Qed.
Lemma lem4342999 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343000 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term287 A s' s) = (term170 A s' s).
Proof. exact (MK_COMB (@lem4342999 A) (@lem4342998 A s' s)). Qed.
Lemma lem4343001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343002 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term288 A s' s) = (term174 A s' s).
Proof. exact (MK_COMB (@lem4343001) (@lem4343000 A s' s)). Qed.
Lemma lem4343003 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term170 B t' t) = (term170 B t' t).
Proof. exact (eq_refl (term170 B t' t)). Qed.
Lemma lem4343004 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term447 A B s' s t' t) = (term176 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343002 A s' s) (@lem4343003 B t' t)). Qed.
Lemma lem4343005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343006 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term449 A B s' s t' t) = (term450 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343005) (@lem4343004 A B s' s t' t)). Qed.
Lemma lem4343007 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term285 A s' s x) = (term162 A s' s x).
Proof. exact (eq_refl (term285 A s' s x)). Qed.
Lemma lem4343008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343009 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term291 A s' s x) = (term292 A s' s x).
Proof. exact (MK_COMB (@lem4343008) (@lem4343007 A s' s x)). Qed.
Lemma lem4343010 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term170 B t' t) = (term170 B t' t).
Proof. exact (eq_refl (term170 B t' t)). Qed.
Lemma lem4343011 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term451 A B s' s x t' t) = (term452 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4343009 A s' s x) (@lem4343010 B t' t)). Qed.
Lemma lem4343012 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term453 A B s' s t' t) = (term454 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343011 A B s' s x t' t)). Qed.
Lemma lem4343013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343014 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term448 A B s' s t' t) = (term455 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343013 A) (@lem4343012 A B s' s t' t)). Qed.
Lemma lem4343015 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term447 A B s' s t' t) = (term448 A B s' s t' t)) = ((term176 A B s' s t' t) = (term455 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4343006 A B s' s t' t) (@lem4343014 A B s' s t' t)). Qed.
Lemma lem4343016 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term176 A B s' s t' t) = (term455 A B s' s t' t).
Proof. exact (EQ_MP (@lem4343015 A B s' s t' t) (@lem4342996 A B s' s t' t)). Qed.
Lemma lem4343018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4343019 {B : Type'} (P : Prop) (Q : B -> Prop) : (term317 B P Q) = (term318 B P Q).
Proof. exact (@lem4343018 B P Q). Qed.
Lemma lem4343020 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term456 A B s' s x t' t) = (term457 A B s' s x t' t).
Proof. exact (@lem4343019 B (term162 A s' s x) (term169 B t' t)). Qed.
Lemma lem4343021 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term285 B t' t x) = (term162 B t' t x).
Proof. exact (eq_refl (term285 B t' t x)). Qed.
Lemma lem4343022 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term286 B t' t) = (term169 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4343021 B t' t x)). Qed.
Lemma lem4343023 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343024 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term287 B t' t) = (term170 B t' t).
Proof. exact (MK_COMB (@lem4343023 B) (@lem4343022 B t' t)). Qed.
Lemma lem4343025 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term292 A s' s x) = (term292 A s' s x).
Proof. exact (eq_refl (term292 A s' s x)). Qed.
Lemma lem4343026 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term456 A B s' s x t' t) = (term452 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4343025 A s' s x) (@lem4343024 B t' t)). Qed.
Lemma lem4343027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343028 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term458 A B s' s x t' t) = (term459 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4343027) (@lem4343026 A B s' s x t' t)). Qed.
Lemma lem4343029 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term285 B t' t x) = (term162 B t' t x).
Proof. exact (eq_refl (term285 B t' t x)). Qed.
Lemma lem4343030 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term292 A s' s x) = (term292 A s' s x).
Proof. exact (eq_refl (term292 A s' s x)). Qed.
Lemma lem4343031 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) (x' : B) : (term460 A B s' s x t' t x') = (term461 A B s' s x t' t x').
Proof. exact (MK_COMB (@lem4343030 A s' s x) (@lem4343029 B t' t x')). Qed.
Lemma lem4343032 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term462 A B s' s x t' t) = (term463 A B s' s x t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343031 A B s' s x t' t x')). Qed.
Lemma lem4343033 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343034 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term457 A B s' s x t' t) = (term464 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4343033 B) (@lem4343032 A B s' s x t' t)). Qed.
Lemma lem4343035 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : ((term456 A B s' s x t' t) = (term457 A B s' s x t' t)) = ((term452 A B s' s x t' t) = (term464 A B s' s x t' t)).
Proof. exact (MK_COMB (@lem4343028 A B s' s x t' t) (@lem4343034 A B s' s x t' t)). Qed.
Lemma lem4343036 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term452 A B s' s x t' t) = (term464 A B s' s x t' t).
Proof. exact (EQ_MP (@lem4343035 A B s' s x t' t) (@lem4343020 A B s' s x t' t)). Qed.
Lemma lem4343037 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term454 A B s' s t' t) = (term465 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343036 A B s' s x t' t)). Qed.
Lemma lem4343038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343039 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term455 A B s' s t' t) = (term466 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343038 A) (@lem4343037 A B s' s t' t)). Qed.
Lemma lem4343040 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term176 A B s' s t' t) = (term466 A B s' s t' t).
Proof. exact (TRANS (@lem4343016 A B s' s t' t) (@lem4343039 A B s' s t' t)). Qed.
Lemma lem4343041 {B : Type'} (t' : B -> Prop) : (term181 B t') = (term181 B t').
Proof. exact (eq_refl (term181 B t')). Qed.
Lemma lem4343042 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term183 A B s' s t' t) = (term467 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343041 B t') (@lem4343040 A B s' s t' t)). Qed.
Lemma lem4343044 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4343045 {B : Type'} (P : B -> Prop) (Q : Prop) : (term234 B P Q) = (term235 B P Q).
Proof. exact (@lem4343044 B P Q). Qed.
Lemma lem4343046 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term467 A B s' s t' t) = (term468 A B s' s t' t).
Proof. exact (@lem4343045 B t' (term466 A B s' s t' t)). Qed.
Lemma lem4343048 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4343049 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem4343048 A P Q). Qed.
Lemma lem4343050 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term469 A B x s' s t' t) = (term470 A B x s' s t' t).
Proof. exact (@lem4343049 A (t' x) (term465 A B s' s t' t)). Qed.
Lemma lem4343051 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term471 A B s' s t' t x) = (term464 A B s' s x t' t).
Proof. exact (eq_refl (term471 A B s' s t' t x)). Qed.
Lemma lem4343052 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term472 A B s' s t' t) = (term465 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343051 A B s' s x t' t)). Qed.
Lemma lem4343053 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343054 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term473 A B s' s t' t) = (term466 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343053 A) (@lem4343052 A B s' s t' t)). Qed.
Lemma lem4343055 {B : Type'} (t' : B -> Prop) (x : B) : (term474 B t' x) = (term474 B t' x).
Proof. exact (eq_refl (term474 B t' x)). Qed.
Lemma lem4343056 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term469 A B x s' s t' t) = (term475 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343055 B t' x) (@lem4343054 A B s' s t' t)). Qed.
Lemma lem4343057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343058 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term476 A B x s' s t' t) = (term477 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343057) (@lem4343056 A B x s' s t' t)). Qed.
Lemma lem4343059 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term471 A B s' s t' t x) = (term464 A B s' s x t' t).
Proof. exact (eq_refl (term471 A B s' s t' t x)). Qed.
Lemma lem4343060 {B : Type'} (t' : B -> Prop) (x : B) : (term474 B t' x) = (term474 B t' x).
Proof. exact (eq_refl (term474 B t' x)). Qed.
Lemma lem4343061 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term478 A B x s' s t' t x') = (term479 A B x s' s x' t' t).
Proof. exact (MK_COMB (@lem4343060 B t' x) (@lem4343059 A B s' s x' t' t)). Qed.
Lemma lem4343062 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term480 A B x s' s t' t) = (term481 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : A => @lem4343061 A B x s' s x' t' t)). Qed.
Lemma lem4343063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343064 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term470 A B x s' s t' t) = (term482 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343063 A) (@lem4343062 A B x s' s t' t)). Qed.
Lemma lem4343065 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term469 A B x s' s t' t) = (term470 A B x s' s t' t)) = ((term475 A B x s' s t' t) = (term482 A B x s' s t' t)).
Proof. exact (MK_COMB (@lem4343058 A B x s' s t' t) (@lem4343064 A B x s' s t' t)). Qed.
Lemma lem4343066 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term475 A B x s' s t' t) = (term482 A B x s' s t' t).
Proof. exact (EQ_MP (@lem4343065 A B x s' s t' t) (@lem4343050 A B x s' s t' t)). Qed.
Lemma lem4343068 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4343069 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4343068 B P Q). Qed.
Lemma lem4343070 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term483 A B x s' s x' t' t) = (term484 A B x s' s x' t' t).
Proof. exact (@lem4343069 B (t' x) (term463 A B s' s x' t' t)). Qed.
Lemma lem4343071 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) (x' : B) : (term485 A B s' s x t' t x') = (term461 A B s' s x t' t x').
Proof. exact (eq_refl (term485 A B s' s x t' t x')). Qed.
Lemma lem4343072 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term486 A B s' s x t' t) = (term463 A B s' s x t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343071 A B s' s x t' t x')). Qed.
Lemma lem4343073 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343074 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) : (term487 A B s' s x t' t) = (term464 A B s' s x t' t).
Proof. exact (MK_COMB (@lem4343073 B) (@lem4343072 A B s' s x t' t)). Qed.
Lemma lem4343075 {B : Type'} (t' : B -> Prop) (x : B) : (term474 B t' x) = (term474 B t' x).
Proof. exact (eq_refl (term474 B t' x)). Qed.
Lemma lem4343076 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term483 A B x s' s x' t' t) = (term479 A B x s' s x' t' t).
Proof. exact (MK_COMB (@lem4343075 B t' x) (@lem4343074 A B s' s x' t' t)). Qed.
Lemma lem4343077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343078 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term488 A B x s' s x' t' t) = (term489 A B x s' s x' t' t).
Proof. exact (MK_COMB (@lem4343077) (@lem4343076 A B x s' s x' t' t)). Qed.
Lemma lem4343079 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) (t' : B -> Prop) (t : B -> Prop) (x' : B) : (term485 A B s' s x t' t x') = (term461 A B s' s x t' t x').
Proof. exact (eq_refl (term485 A B s' s x t' t x')). Qed.
Lemma lem4343080 {B : Type'} (t' : B -> Prop) (x : B) : (term474 B t' x) = (term474 B t' x).
Proof. exact (eq_refl (term474 B t' x)). Qed.
Lemma lem4343081 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) (x'' : B) : (term490 A B x s' s x' t' t x'') = (term491 A B x s' s x' t' t x'').
Proof. exact (MK_COMB (@lem4343080 B t' x) (@lem4343079 A B s' s x' t' t x'')). Qed.
Lemma lem4343082 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term492 A B x s' s x' t' t) = (term493 A B x s' s x' t' t).
Proof. exact (fun_ext (fun x'' : B => @lem4343081 A B x s' s x' t' t x'')). Qed.
Lemma lem4343083 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343084 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term484 A B x s' s x' t' t) = (term494 A B x s' s x' t' t).
Proof. exact (MK_COMB (@lem4343083 B) (@lem4343082 A B x s' s x' t' t)). Qed.
Lemma lem4343085 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : ((term483 A B x s' s x' t' t) = (term484 A B x s' s x' t' t)) = ((term479 A B x s' s x' t' t) = (term494 A B x s' s x' t' t)).
Proof. exact (MK_COMB (@lem4343078 A B x s' s x' t' t) (@lem4343084 A B x s' s x' t' t)). Qed.
Lemma lem4343086 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term479 A B x s' s x' t' t) = (term494 A B x s' s x' t' t).
Proof. exact (EQ_MP (@lem4343085 A B x s' s x' t' t) (@lem4343070 A B x s' s x' t' t)). Qed.
Lemma lem4343087 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term481 A B x s' s t' t) = (term495 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : A => @lem4343086 A B x s' s x' t' t)). Qed.
Lemma lem4343088 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343089 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term482 A B x s' s t' t) = (term496 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343088 A) (@lem4343087 A B x s' s t' t)). Qed.
Lemma lem4343090 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term475 A B x s' s t' t) = (term496 A B x s' s t' t).
Proof. exact (TRANS (@lem4343066 A B x s' s t' t) (@lem4343089 A B x s' s t' t)). Qed.
Lemma lem4343091 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term497 A B s' s t' t) = (term498 A B s' s t' t).
Proof. exact (fun_ext (fun x : B => @lem4343090 A B x s' s t' t)). Qed.
Lemma lem4343092 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343093 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term468 A B s' s t' t) = (term499 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343092 B) (@lem4343091 A B s' s t' t)). Qed.
Lemma lem4343094 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term467 A B s' s t' t) = (term499 A B s' s t' t).
Proof. exact (TRANS (@lem4343046 A B s' s t' t) (@lem4343093 A B s' s t' t)). Qed.
Lemma lem4343095 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term183 A B s' s t' t) = (term499 A B s' s t' t).
Proof. exact (TRANS (@lem4343042 A B s' s t' t) (@lem4343094 A B s' s t' t)). Qed.
Lemma lem4343096 {A : Type'} (s' : A -> Prop) : (term181 A s') = (term181 A s').
Proof. exact (eq_refl (term181 A s')). Qed.
Lemma lem4343097 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term187 A B s' s t' t) = (term500 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343096 A s') (@lem4343095 A B s' s t' t)). Qed.
Lemma lem4343099 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4343100 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4343099 A P Q). Qed.
Lemma lem4343101 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term500 A B s' s t' t) = (term501 A B s' s t' t).
Proof. exact (@lem4343100 A s' (term499 A B s' s t' t)). Qed.
Lemma lem4343103 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4343104 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4343103 B P Q). Qed.
Lemma lem4343105 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term502 A B x s' s t' t) = (term503 A B x s' s t' t).
Proof. exact (@lem4343104 B (s' x) (term498 A B s' s t' t)). Qed.
Lemma lem4343106 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term504 A B s' s t' t x) = (term496 A B x s' s t' t).
Proof. exact (eq_refl (term504 A B s' s t' t x)). Qed.
Lemma lem4343107 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term505 A B s' s t' t) = (term498 A B s' s t' t).
Proof. exact (fun_ext (fun x : B => @lem4343106 A B x s' s t' t)). Qed.
Lemma lem4343108 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343109 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term506 A B s' s t' t) = (term499 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343108 B) (@lem4343107 A B s' s t' t)). Qed.
Lemma lem4343110 {A : Type'} (s' : A -> Prop) (x : A) : (term474 A s' x) = (term474 A s' x).
Proof. exact (eq_refl (term474 A s' x)). Qed.
Lemma lem4343111 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term502 A B x s' s t' t) = (term507 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343110 A s' x) (@lem4343109 A B s' s t' t)). Qed.
Lemma lem4343112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343113 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term508 A B x s' s t' t) = (term509 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343112) (@lem4343111 A B x s' s t' t)). Qed.
Lemma lem4343114 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term504 A B s' s t' t x) = (term496 A B x s' s t' t).
Proof. exact (eq_refl (term504 A B s' s t' t x)). Qed.
Lemma lem4343115 {A : Type'} (s' : A -> Prop) (x : A) : (term474 A s' x) = (term474 A s' x).
Proof. exact (eq_refl (term474 A s' x)). Qed.
Lemma lem4343116 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term510 A B x s' s t' t x') = (term511 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343115 A s' x) (@lem4343114 A B x' s' s t' t)). Qed.
Lemma lem4343117 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term512 A B x s' s t' t) = (term513 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343116 A B x x' s' s t' t)). Qed.
Lemma lem4343118 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343119 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term503 A B x s' s t' t) = (term514 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343118 B) (@lem4343117 A B x s' s t' t)). Qed.
Lemma lem4343120 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term502 A B x s' s t' t) = (term503 A B x s' s t' t)) = ((term507 A B x s' s t' t) = (term514 A B x s' s t' t)).
Proof. exact (MK_COMB (@lem4343113 A B x s' s t' t) (@lem4343119 A B x s' s t' t)). Qed.
Lemma lem4343121 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term507 A B x s' s t' t) = (term514 A B x s' s t' t).
Proof. exact (EQ_MP (@lem4343120 A B x s' s t' t) (@lem4343105 A B x s' s t' t)). Qed.
Lemma lem4343123 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4343124 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem4343123 A P Q). Qed.
Lemma lem4343125 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term515 A B x x' s' s t' t) = (term516 A B x x' s' s t' t).
Proof. exact (@lem4343124 A (s' x) (term495 A B x' s' s t' t)). Qed.
Lemma lem4343126 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term517 A B x s' s t' t x') = (term494 A B x s' s x' t' t).
Proof. exact (eq_refl (term517 A B x s' s t' t x')). Qed.
Lemma lem4343127 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term518 A B x s' s t' t) = (term495 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : A => @lem4343126 A B x s' s x' t' t)). Qed.
Lemma lem4343128 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343129 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term519 A B x s' s t' t) = (term496 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343128 A) (@lem4343127 A B x s' s t' t)). Qed.
Lemma lem4343130 {A : Type'} (s' : A -> Prop) (x : A) : (term474 A s' x) = (term474 A s' x).
Proof. exact (eq_refl (term474 A s' x)). Qed.
Lemma lem4343131 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term515 A B x x' s' s t' t) = (term511 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343130 A s' x) (@lem4343129 A B x' s' s t' t)). Qed.
Lemma lem4343132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343133 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term520 A B x x' s' s t' t) = (term521 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343132) (@lem4343131 A B x x' s' s t' t)). Qed.
Lemma lem4343134 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term517 A B x s' s t' t x') = (term494 A B x s' s x' t' t).
Proof. exact (eq_refl (term517 A B x s' s t' t x')). Qed.
Lemma lem4343135 {A : Type'} (s' : A -> Prop) (x : A) : (term474 A s' x) = (term474 A s' x).
Proof. exact (eq_refl (term474 A s' x)). Qed.
Lemma lem4343136 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term522 A B x x' s' s t' t x'') = (term523 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343135 A s' x) (@lem4343134 A B x' s' s x'' t' t)). Qed.
Lemma lem4343137 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term524 A B x x' s' s t' t) = (term525 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343136 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343138 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343139 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term516 A B x x' s' s t' t) = (term526 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343138 A) (@lem4343137 A B x x' s' s t' t)). Qed.
Lemma lem4343140 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term515 A B x x' s' s t' t) = (term516 A B x x' s' s t' t)) = ((term511 A B x x' s' s t' t) = (term526 A B x x' s' s t' t)).
Proof. exact (MK_COMB (@lem4343133 A B x x' s' s t' t) (@lem4343139 A B x x' s' s t' t)). Qed.
Lemma lem4343141 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term511 A B x x' s' s t' t) = (term526 A B x x' s' s t' t).
Proof. exact (EQ_MP (@lem4343140 A B x x' s' s t' t) (@lem4343125 A B x x' s' s t' t)). Qed.
Lemma lem4343143 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4343144 {B : Type'} (P : Prop) (Q : B -> Prop) : (term237 B P Q) = (term238 B P Q).
Proof. exact (@lem4343143 B P Q). Qed.
Lemma lem4343145 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term527 A B x x' s' s x'' t' t) = (term528 A B x x' s' s x'' t' t).
Proof. exact (@lem4343144 B (s' x) (term493 A B x' s' s x'' t' t)). Qed.
Lemma lem4343146 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) (x'' : B) : (term529 A B x s' s x' t' t x'') = (term491 A B x s' s x' t' t x'').
Proof. exact (eq_refl (term529 A B x s' s x' t' t x'')). Qed.
Lemma lem4343147 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term530 A B x s' s x' t' t) = (term493 A B x s' s x' t' t).
Proof. exact (fun_ext (fun x'' : B => @lem4343146 A B x s' s x' t' t x'')). Qed.
Lemma lem4343148 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343149 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) : (term531 A B x s' s x' t' t) = (term494 A B x s' s x' t' t).
Proof. exact (MK_COMB (@lem4343148 B) (@lem4343147 A B x s' s x' t' t)). Qed.
Lemma lem4343150 {A : Type'} (s' : A -> Prop) (x : A) : (term474 A s' x) = (term474 A s' x).
Proof. exact (eq_refl (term474 A s' x)). Qed.
Lemma lem4343151 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term527 A B x x' s' s x'' t' t) = (term523 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343150 A s' x) (@lem4343149 A B x' s' s x'' t' t)). Qed.
Lemma lem4343152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343153 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term532 A B x x' s' s x'' t' t) = (term533 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343152) (@lem4343151 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343154 {A B : Type'} (x : B) (s' : A -> Prop) (s : A -> Prop) (x' : A) (t' : B -> Prop) (t : B -> Prop) (x'' : B) : (term529 A B x s' s x' t' t x'') = (term491 A B x s' s x' t' t x'').
Proof. exact (eq_refl (term529 A B x s' s x' t' t x'')). Qed.
Lemma lem4343155 {A : Type'} (s' : A -> Prop) (x : A) : (term474 A s' x) = (term474 A s' x).
Proof. exact (eq_refl (term474 A s' x)). Qed.
Lemma lem4343156 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term534 A B x x' s' s x'' t' t x''') = (term535 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4343155 A s' x) (@lem4343154 A B x' s' s x'' t' t x''')). Qed.
Lemma lem4343157 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term536 A B x x' s' s x'' t' t) = (term537 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343156 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343158 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343159 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term528 A B x x' s' s x'' t' t) = (term538 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343158 B) (@lem4343157 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343160 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : ((term527 A B x x' s' s x'' t' t) = (term528 A B x x' s' s x'' t' t)) = ((term523 A B x x' s' s x'' t' t) = (term538 A B x x' s' s x'' t' t)).
Proof. exact (MK_COMB (@lem4343153 A B x x' s' s x'' t' t) (@lem4343159 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343161 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term523 A B x x' s' s x'' t' t) = (term538 A B x x' s' s x'' t' t).
Proof. exact (EQ_MP (@lem4343160 A B x x' s' s x'' t' t) (@lem4343145 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343162 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term525 A B x x' s' s t' t) = (term539 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343161 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343163 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343164 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term526 A B x x' s' s t' t) = (term540 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343163 A) (@lem4343162 A B x x' s' s t' t)). Qed.
Lemma lem4343165 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term511 A B x x' s' s t' t) = (term540 A B x x' s' s t' t).
Proof. exact (TRANS (@lem4343141 A B x x' s' s t' t) (@lem4343164 A B x x' s' s t' t)). Qed.
Lemma lem4343166 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term513 A B x s' s t' t) = (term541 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343165 A B x x' s' s t' t)). Qed.
Lemma lem4343167 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343168 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term514 A B x s' s t' t) = (term542 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343167 B) (@lem4343166 A B x s' s t' t)). Qed.
Lemma lem4343169 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term507 A B x s' s t' t) = (term542 A B x s' s t' t).
Proof. exact (TRANS (@lem4343121 A B x s' s t' t) (@lem4343168 A B x s' s t' t)). Qed.
Lemma lem4343170 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term543 A B s' s t' t) = (term544 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343169 A B x s' s t' t)). Qed.
Lemma lem4343171 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343172 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term501 A B s' s t' t) = (term545 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343171 A) (@lem4343170 A B s' s t' t)). Qed.
Lemma lem4343173 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term500 A B s' s t' t) = (term545 A B s' s t' t).
Proof. exact (TRANS (@lem4343101 A B s' s t' t) (@lem4343172 A B s' s t' t)). Qed.
Lemma lem4343174 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term187 A B s' s t' t) = (term545 A B s' s t' t).
Proof. exact (TRANS (@lem4343097 A B s' s t' t) (@lem4343173 A B s' s t' t)). Qed.
Lemma lem4343175 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term193 A B s' s t' t) = (term547 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342990 A B s s' t t') (@lem4343174 A B s' s t' t)). Qed.
Lemma lem4343177 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343178 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (@lem4343177 A P Q). Qed.
Lemma lem4343179 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term548 A B s' s t' t) = (term549 A B s' s t' t).
Proof. exact (@lem4343178 A (term544 A B s s' t t') (term544 A B s' s t' t)). Qed.
Lemma lem4343180 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term550 A B s s' t t' x) = (term542 A B x s s' t t').
Proof. exact (eq_refl (term550 A B s s' t t' x)). Qed.
Lemma lem4343181 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term551 A B s s' t t') = (term544 A B s s' t t').
Proof. exact (fun_ext (fun x : A => @lem4343180 A B x s s' t t')). Qed.
Lemma lem4343182 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343183 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term552 A B s s' t t') = (term545 A B s s' t t').
Proof. exact (MK_COMB (@lem4343182 A) (@lem4343181 A B s s' t t')). Qed.
Lemma lem4343184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343185 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term553 A B s s' t t') = (term546 A B s s' t t').
Proof. exact (MK_COMB (@lem4343184) (@lem4343183 A B s s' t t')). Qed.
Lemma lem4343186 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term550 A B s' s t' t x) = (term542 A B x s' s t' t).
Proof. exact (eq_refl (term550 A B s' s t' t x)). Qed.
Lemma lem4343187 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term551 A B s' s t' t) = (term544 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343186 A B x s' s t' t)). Qed.
Lemma lem4343188 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343189 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term552 A B s' s t' t) = (term545 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343188 A) (@lem4343187 A B s' s t' t)). Qed.
Lemma lem4343190 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term548 A B s' s t' t) = (term547 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343185 A B s s' t t') (@lem4343189 A B s' s t' t)). Qed.
Lemma lem4343191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343192 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term554 A B s' s t' t) = (term555 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343191) (@lem4343190 A B s' s t' t)). Qed.
Lemma lem4343193 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term550 A B s s' t t' x) = (term542 A B x s s' t t').
Proof. exact (eq_refl (term550 A B s s' t t' x)). Qed.
Lemma lem4343194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343195 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term556 A B s s' t t' x) = (term557 A B x s s' t t').
Proof. exact (MK_COMB (@lem4343194) (@lem4343193 A B x s s' t t')). Qed.
Lemma lem4343196 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term550 A B s' s t' t x) = (term542 A B x s' s t' t).
Proof. exact (eq_refl (term550 A B s' s t' t x)). Qed.
Lemma lem4343197 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term558 A B s' s t' t x) = (term559 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343195 A B x s s' t t') (@lem4343196 A B x s' s t' t)). Qed.
Lemma lem4343198 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term560 A B s' s t' t) = (term561 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343197 A B x s' s t' t)). Qed.
Lemma lem4343199 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343200 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term549 A B s' s t' t) = (term562 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343199 A) (@lem4343198 A B s' s t' t)). Qed.
Lemma lem4343201 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term548 A B s' s t' t) = (term549 A B s' s t' t)) = ((term547 A B s' s t' t) = (term562 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4343192 A B s' s t' t) (@lem4343200 A B s' s t' t)). Qed.
Lemma lem4343202 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term547 A B s' s t' t) = (term562 A B s' s t' t).
Proof. exact (EQ_MP (@lem4343201 A B s' s t' t) (@lem4343179 A B s' s t' t)). Qed.
Lemma lem4343204 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343205 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term246 B P Q) = (term247 B P Q).
Proof. exact (@lem4343204 B P Q). Qed.
Lemma lem4343206 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term563 A B x s' s t' t) = (term564 A B x s' s t' t).
Proof. exact (@lem4343205 B (term541 A B x s s' t t') (term541 A B x s' s t' t)). Qed.
Lemma lem4343207 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term565 A B x s s' t t' x') = (term540 A B x x' s s' t t').
Proof. exact (eq_refl (term565 A B x s s' t t' x')). Qed.
Lemma lem4343208 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term566 A B x s s' t t') = (term541 A B x s s' t t').
Proof. exact (fun_ext (fun x' : B => @lem4343207 A B x x' s s' t t')). Qed.
Lemma lem4343209 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343210 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term567 A B x s s' t t') = (term542 A B x s s' t t').
Proof. exact (MK_COMB (@lem4343209 B) (@lem4343208 A B x s s' t t')). Qed.
Lemma lem4343211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343212 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term568 A B x s s' t t') = (term557 A B x s s' t t').
Proof. exact (MK_COMB (@lem4343211) (@lem4343210 A B x s s' t t')). Qed.
Lemma lem4343213 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term565 A B x s' s t' t x') = (term540 A B x x' s' s t' t).
Proof. exact (eq_refl (term565 A B x s' s t' t x')). Qed.
Lemma lem4343214 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term566 A B x s' s t' t) = (term541 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343213 A B x x' s' s t' t)). Qed.
Lemma lem4343215 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343216 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term567 A B x s' s t' t) = (term542 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343215 B) (@lem4343214 A B x s' s t' t)). Qed.
Lemma lem4343217 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term563 A B x s' s t' t) = (term559 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343212 A B x s s' t t') (@lem4343216 A B x s' s t' t)). Qed.
Lemma lem4343218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343219 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term569 A B x s' s t' t) = (term570 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343218) (@lem4343217 A B x s' s t' t)). Qed.
Lemma lem4343220 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term565 A B x s s' t t' x') = (term540 A B x x' s s' t t').
Proof. exact (eq_refl (term565 A B x s s' t t' x')). Qed.
Lemma lem4343221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343222 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term571 A B x s s' t t' x') = (term572 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4343221) (@lem4343220 A B x x' s s' t t')). Qed.
Lemma lem4343223 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term565 A B x s' s t' t x') = (term540 A B x x' s' s t' t).
Proof. exact (eq_refl (term565 A B x s' s t' t x')). Qed.
Lemma lem4343224 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term573 A B x s' s t' t x') = (term574 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343222 A B x x' s s' t t') (@lem4343223 A B x x' s' s t' t)). Qed.
Lemma lem4343225 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term575 A B x s' s t' t) = (term576 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343224 A B x x' s' s t' t)). Qed.
Lemma lem4343226 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343227 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term564 A B x s' s t' t) = (term577 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343226 B) (@lem4343225 A B x s' s t' t)). Qed.
Lemma lem4343228 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term563 A B x s' s t' t) = (term564 A B x s' s t' t)) = ((term559 A B x s' s t' t) = (term577 A B x s' s t' t)).
Proof. exact (MK_COMB (@lem4343219 A B x s' s t' t) (@lem4343227 A B x s' s t' t)). Qed.
Lemma lem4343229 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term559 A B x s' s t' t) = (term577 A B x s' s t' t).
Proof. exact (EQ_MP (@lem4343228 A B x s' s t' t) (@lem4343206 A B x s' s t' t)). Qed.
Lemma lem4343231 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343232 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (@lem4343231 A P Q). Qed.
Lemma lem4343233 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term578 A B x x' s' s t' t) = (term579 A B x x' s' s t' t).
Proof. exact (@lem4343232 A (term539 A B x x' s s' t t') (term539 A B x x' s' s t' t)). Qed.
Lemma lem4343234 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term580 A B x x' s s' t t' x'') = (term538 A B x x' s s' x'' t t').
Proof. exact (eq_refl (term580 A B x x' s s' t t' x'')). Qed.
Lemma lem4343235 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term581 A B x x' s s' t t') = (term539 A B x x' s s' t t').
Proof. exact (fun_ext (fun x'' : A => @lem4343234 A B x x' s s' x'' t t')). Qed.
Lemma lem4343236 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343237 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term582 A B x x' s s' t t') = (term540 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4343236 A) (@lem4343235 A B x x' s s' t t')). Qed.
Lemma lem4343238 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343239 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term583 A B x x' s s' t t') = (term572 A B x x' s s' t t').
Proof. exact (MK_COMB (@lem4343238) (@lem4343237 A B x x' s s' t t')). Qed.
Lemma lem4343240 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term580 A B x x' s' s t' t x'') = (term538 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term580 A B x x' s' s t' t x'')). Qed.
Lemma lem4343241 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term581 A B x x' s' s t' t) = (term539 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343240 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343242 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343243 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term582 A B x x' s' s t' t) = (term540 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343242 A) (@lem4343241 A B x x' s' s t' t)). Qed.
Lemma lem4343244 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term578 A B x x' s' s t' t) = (term574 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343239 A B x x' s s' t t') (@lem4343243 A B x x' s' s t' t)). Qed.
Lemma lem4343245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343246 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term584 A B x x' s' s t' t) = (term585 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343245) (@lem4343244 A B x x' s' s t' t)). Qed.
Lemma lem4343247 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term580 A B x x' s s' t t' x'') = (term538 A B x x' s s' x'' t t').
Proof. exact (eq_refl (term580 A B x x' s s' t t' x'')). Qed.
Lemma lem4343248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343249 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term586 A B x x' s s' t t' x'') = (term587 A B x x' s s' x'' t t').
Proof. exact (MK_COMB (@lem4343248) (@lem4343247 A B x x' s s' x'' t t')). Qed.
Lemma lem4343250 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term580 A B x x' s' s t' t x'') = (term538 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term580 A B x x' s' s t' t x'')). Qed.
Lemma lem4343251 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term588 A B x x' s' s t' t x'') = (term589 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343249 A B x x' s s' x'' t t') (@lem4343250 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343252 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term590 A B x x' s' s t' t) = (term591 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343251 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343253 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343254 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term579 A B x x' s' s t' t) = (term592 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343253 A) (@lem4343252 A B x x' s' s t' t)). Qed.
Lemma lem4343255 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term578 A B x x' s' s t' t) = (term579 A B x x' s' s t' t)) = ((term574 A B x x' s' s t' t) = (term592 A B x x' s' s t' t)).
Proof. exact (MK_COMB (@lem4343246 A B x x' s' s t' t) (@lem4343254 A B x x' s' s t' t)). Qed.
Lemma lem4343256 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term574 A B x x' s' s t' t) = (term592 A B x x' s' s t' t).
Proof. exact (EQ_MP (@lem4343255 A B x x' s' s t' t) (@lem4343233 A B x x' s' s t' t)). Qed.
Lemma lem4343258 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343259 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term246 B P Q) = (term247 B P Q).
Proof. exact (@lem4343258 B P Q). Qed.
Lemma lem4343260 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term593 A B x x' s' s x'' t' t) = (term594 A B x x' s' s x'' t' t).
Proof. exact (@lem4343259 B (term537 A B x x' s s' x'' t t') (term537 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343261 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) : (term595 A B x x' s s' x'' t t' x''') = (term535 A B x x' s s' x'' t t' x''').
Proof. exact (eq_refl (term595 A B x x' s s' x'' t t' x''')). Qed.
Lemma lem4343262 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term596 A B x x' s s' x'' t t') = (term537 A B x x' s s' x'' t t').
Proof. exact (fun_ext (fun x''' : B => @lem4343261 A B x x' s s' x'' t t' x''')). Qed.
Lemma lem4343263 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343264 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term597 A B x x' s s' x'' t t') = (term538 A B x x' s s' x'' t t').
Proof. exact (MK_COMB (@lem4343263 B) (@lem4343262 A B x x' s s' x'' t t')). Qed.
Lemma lem4343265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343266 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) : (term598 A B x x' s s' x'' t t') = (term587 A B x x' s s' x'' t t').
Proof. exact (MK_COMB (@lem4343265) (@lem4343264 A B x x' s s' x'' t t')). Qed.
Lemma lem4343267 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term595 A B x x' s' s x'' t' t x''') = (term535 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term595 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343268 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term596 A B x x' s' s x'' t' t) = (term537 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343267 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343269 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343270 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term597 A B x x' s' s x'' t' t) = (term538 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343269 B) (@lem4343268 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343271 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term593 A B x x' s' s x'' t' t) = (term589 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343266 A B x x' s s' x'' t t') (@lem4343270 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343273 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term599 A B x x' s' s x'' t' t) = (term600 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343272) (@lem4343271 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343274 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) : (term595 A B x x' s s' x'' t t' x''') = (term535 A B x x' s s' x'' t t' x''').
Proof. exact (eq_refl (term595 A B x x' s s' x'' t t' x''')). Qed.
Lemma lem4343275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343276 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) : (term601 A B x x' s s' x'' t t' x''') = (term602 A B x x' s s' x'' t t' x''').
Proof. exact (MK_COMB (@lem4343275) (@lem4343274 A B x x' s s' x'' t t' x''')). Qed.
Lemma lem4343277 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term595 A B x x' s' s x'' t' t x''') = (term535 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term595 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343278 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term603 A B x x' s' s x'' t' t x''') = (term604 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4343276 A B x x' s s' x'' t t' x''') (@lem4343277 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343279 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term605 A B x x' s' s x'' t' t) = (term606 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343278 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343280 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343281 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term594 A B x x' s' s x'' t' t) = (term607 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343280 B) (@lem4343279 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343282 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : ((term593 A B x x' s' s x'' t' t) = (term594 A B x x' s' s x'' t' t)) = ((term589 A B x x' s' s x'' t' t) = (term607 A B x x' s' s x'' t' t)).
Proof. exact (MK_COMB (@lem4343273 A B x x' s' s x'' t' t) (@lem4343281 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343283 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term589 A B x x' s' s x'' t' t) = (term607 A B x x' s' s x'' t' t).
Proof. exact (EQ_MP (@lem4343282 A B x x' s' s x'' t' t) (@lem4343260 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343284 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term591 A B x x' s' s t' t) = (term608 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343283 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343285 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343286 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term592 A B x x' s' s t' t) = (term609 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343285 A) (@lem4343284 A B x x' s' s t' t)). Qed.
Lemma lem4343287 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term574 A B x x' s' s t' t) = (term609 A B x x' s' s t' t).
Proof. exact (TRANS (@lem4343256 A B x x' s' s t' t) (@lem4343286 A B x x' s' s t' t)). Qed.
Lemma lem4343288 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term576 A B x s' s t' t) = (term610 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343287 A B x x' s' s t' t)). Qed.
Lemma lem4343289 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343290 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term577 A B x s' s t' t) = (term611 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343289 B) (@lem4343288 A B x s' s t' t)). Qed.
Lemma lem4343291 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term559 A B x s' s t' t) = (term611 A B x s' s t' t).
Proof. exact (TRANS (@lem4343229 A B x s' s t' t) (@lem4343290 A B x s' s t' t)). Qed.
Lemma lem4343292 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term561 A B s' s t' t) = (term612 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343291 A B x s' s t' t)). Qed.
Lemma lem4343293 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343294 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term562 A B s' s t' t) = (term613 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343293 A) (@lem4343292 A B s' s t' t)). Qed.
Lemma lem4343295 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term547 A B s' s t' t) = (term613 A B s' s t' t).
Proof. exact (TRANS (@lem4343202 A B s' s t' t) (@lem4343294 A B s' s t' t)). Qed.
Lemma lem4343296 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term193 A B s' s t' t) = (term613 A B s' s t' t).
Proof. exact (TRANS (@lem4343175 A B s' s t' t) (@lem4343295 A B s' s t' t)). Qed.
Lemma lem4343297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343298 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term223 A B s' s t' t) = (term614 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343297) (@lem4343296 A B s' s t' t)). Qed.
Lemma lem4343299 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343300 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term225 A B s' s t' t) = (term615 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343298 A B s' s t' t) (@lem4343299 A B s' s t' t)). Qed.
Lemma lem4343302 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4343303 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4343302 A P Q). Qed.
Lemma lem4343304 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term616 A B s' s t' t) = (term617 A B s' s t' t).
Proof. exact (@lem4343303 A (term612 A B s' s t' t) (term221 A B s' s t' t)). Qed.
Lemma lem4343305 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term618 A B s' s t' t x) = (term611 A B x s' s t' t).
Proof. exact (eq_refl (term618 A B s' s t' t x)). Qed.
Lemma lem4343306 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term619 A B s' s t' t) = (term612 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343305 A B x s' s t' t)). Qed.
Lemma lem4343307 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343308 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term620 A B s' s t' t) = (term613 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343307 A) (@lem4343306 A B s' s t' t)). Qed.
Lemma lem4343309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343310 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term621 A B s' s t' t) = (term614 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343309) (@lem4343308 A B s' s t' t)). Qed.
Lemma lem4343311 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343312 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term616 A B s' s t' t) = (term615 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343310 A B s' s t' t) (@lem4343311 A B s' s t' t)). Qed.
Lemma lem4343313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343314 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term622 A B s' s t' t) = (term623 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343313) (@lem4343312 A B s' s t' t)). Qed.
Lemma lem4343315 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term618 A B s' s t' t x) = (term611 A B x s' s t' t).
Proof. exact (eq_refl (term618 A B s' s t' t x)). Qed.
Lemma lem4343316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343317 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term624 A B s' s t' t x) = (term625 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343316) (@lem4343315 A B x s' s t' t)). Qed.
Lemma lem4343318 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343319 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term626 A B x s' s t' t) = (term627 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343317 A B x s' s t' t) (@lem4343318 A B s' s t' t)). Qed.
Lemma lem4343320 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term628 A B s' s t' t) = (term629 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343319 A B x s' s t' t)). Qed.
Lemma lem4343321 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343322 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term617 A B s' s t' t) = (term630 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343321 A) (@lem4343320 A B s' s t' t)). Qed.
Lemma lem4343323 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term616 A B s' s t' t) = (term617 A B s' s t' t)) = ((term615 A B s' s t' t) = (term630 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4343314 A B s' s t' t) (@lem4343322 A B s' s t' t)). Qed.
Lemma lem4343324 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term615 A B s' s t' t) = (term630 A B s' s t' t).
Proof. exact (EQ_MP (@lem4343323 A B s' s t' t) (@lem4343304 A B s' s t' t)). Qed.
Lemma lem4343326 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4343327 {B : Type'} (P : B -> Prop) (Q : Prop) : (term234 B P Q) = (term235 B P Q).
Proof. exact (@lem4343326 B P Q). Qed.
Lemma lem4343328 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term631 A B x s' s t' t) = (term632 A B x s' s t' t).
Proof. exact (@lem4343327 B (term610 A B x s' s t' t) (term221 A B s' s t' t)). Qed.
Lemma lem4343329 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term633 A B x s' s t' t x') = (term609 A B x x' s' s t' t).
Proof. exact (eq_refl (term633 A B x s' s t' t x')). Qed.
Lemma lem4343330 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term634 A B x s' s t' t) = (term610 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343329 A B x x' s' s t' t)). Qed.
Lemma lem4343331 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343332 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term635 A B x s' s t' t) = (term611 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343331 B) (@lem4343330 A B x s' s t' t)). Qed.
Lemma lem4343333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343334 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term636 A B x s' s t' t) = (term625 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343333) (@lem4343332 A B x s' s t' t)). Qed.
Lemma lem4343335 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343336 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term631 A B x s' s t' t) = (term627 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343334 A B x s' s t' t) (@lem4343335 A B s' s t' t)). Qed.
Lemma lem4343337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343338 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term637 A B x s' s t' t) = (term638 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343337) (@lem4343336 A B x s' s t' t)). Qed.
Lemma lem4343339 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term633 A B x s' s t' t x') = (term609 A B x x' s' s t' t).
Proof. exact (eq_refl (term633 A B x s' s t' t x')). Qed.
Lemma lem4343340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343341 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term639 A B x s' s t' t x') = (term640 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343340) (@lem4343339 A B x x' s' s t' t)). Qed.
Lemma lem4343342 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343343 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term641 A B x x' s' s t' t) = (term642 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343341 A B x x' s' s t' t) (@lem4343342 A B s' s t' t)). Qed.
Lemma lem4343344 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term643 A B x s' s t' t) = (term644 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343343 A B x x' s' s t' t)). Qed.
Lemma lem4343345 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343346 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term632 A B x s' s t' t) = (term645 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343345 B) (@lem4343344 A B x s' s t' t)). Qed.
Lemma lem4343347 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term631 A B x s' s t' t) = (term632 A B x s' s t' t)) = ((term627 A B x s' s t' t) = (term645 A B x s' s t' t)).
Proof. exact (MK_COMB (@lem4343338 A B x s' s t' t) (@lem4343346 A B x s' s t' t)). Qed.
Lemma lem4343348 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term627 A B x s' s t' t) = (term645 A B x s' s t' t).
Proof. exact (EQ_MP (@lem4343347 A B x s' s t' t) (@lem4343328 A B x s' s t' t)). Qed.
Lemma lem4343350 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4343351 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (@lem4343350 A P Q). Qed.
Lemma lem4343352 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term646 A B x x' s' s t' t) = (term647 A B x x' s' s t' t).
Proof. exact (@lem4343351 A (term608 A B x x' s' s t' t) (term221 A B s' s t' t)). Qed.
Lemma lem4343353 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term648 A B x x' s' s t' t x'') = (term607 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term648 A B x x' s' s t' t x'')). Qed.
Lemma lem4343354 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term649 A B x x' s' s t' t) = (term608 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343353 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343355 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343356 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term650 A B x x' s' s t' t) = (term609 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343355 A) (@lem4343354 A B x x' s' s t' t)). Qed.
Lemma lem4343357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343358 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term651 A B x x' s' s t' t) = (term640 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343357) (@lem4343356 A B x x' s' s t' t)). Qed.
Lemma lem4343359 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343360 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term646 A B x x' s' s t' t) = (term642 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343358 A B x x' s' s t' t) (@lem4343359 A B s' s t' t)). Qed.
Lemma lem4343361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343362 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term652 A B x x' s' s t' t) = (term653 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343361) (@lem4343360 A B x x' s' s t' t)). Qed.
Lemma lem4343363 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term648 A B x x' s' s t' t x'') = (term607 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term648 A B x x' s' s t' t x'')). Qed.
Lemma lem4343364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343365 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term654 A B x x' s' s t' t x'') = (term655 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343364) (@lem4343363 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343366 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343367 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term656 A B x x' x'' s' s t' t) = (term657 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343365 A B x x' s' s x'' t' t) (@lem4343366 A B s' s t' t)). Qed.
Lemma lem4343368 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term658 A B x x' s' s t' t) = (term659 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343367 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343369 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343370 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term647 A B x x' s' s t' t) = (term660 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343369 A) (@lem4343368 A B x x' s' s t' t)). Qed.
Lemma lem4343371 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term646 A B x x' s' s t' t) = (term647 A B x x' s' s t' t)) = ((term642 A B x x' s' s t' t) = (term660 A B x x' s' s t' t)).
Proof. exact (MK_COMB (@lem4343362 A B x x' s' s t' t) (@lem4343370 A B x x' s' s t' t)). Qed.
Lemma lem4343372 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term642 A B x x' s' s t' t) = (term660 A B x x' s' s t' t).
Proof. exact (EQ_MP (@lem4343371 A B x x' s' s t' t) (@lem4343352 A B x x' s' s t' t)). Qed.
Lemma lem4343374 {A : Type'} (P : A -> Prop) (Q : Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4343375 {B : Type'} (P : B -> Prop) (Q : Prop) : (term234 B P Q) = (term235 B P Q).
Proof. exact (@lem4343374 B P Q). Qed.
Lemma lem4343376 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term661 A B x x' x'' s' s t' t) = (term662 A B x x' x'' s' s t' t).
Proof. exact (@lem4343375 B (term606 A B x x' s' s x'' t' t) (term221 A B s' s t' t)). Qed.
Lemma lem4343377 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term663 A B x x' s' s x'' t' t x''') = (term604 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term663 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343378 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term664 A B x x' s' s x'' t' t) = (term606 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343377 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343379 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343380 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term665 A B x x' s' s x'' t' t) = (term607 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343379 B) (@lem4343378 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343382 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term666 A B x x' s' s x'' t' t) = (term655 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343381) (@lem4343380 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343383 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343384 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term661 A B x x' x'' s' s t' t) = (term657 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343382 A B x x' s' s x'' t' t) (@lem4343383 A B s' s t' t)). Qed.
Lemma lem4343385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343386 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term667 A B x x' x'' s' s t' t) = (term668 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343385) (@lem4343384 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343387 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term663 A B x x' s' s x'' t' t x''') = (term604 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term663 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343389 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term669 A B x x' s' s x'' t' t x''') = (term670 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4343388) (@lem4343387 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343390 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (eq_refl (term221 A B s' s t' t)). Qed.
Lemma lem4343391 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term671 A B x x' x'' x''' s' s t' t) = (term672 A B x x' x'' x''' s' s t' t).
Proof. exact (MK_COMB (@lem4343389 A B x x' s' s x'' t' t x''') (@lem4343390 A B s' s t' t)). Qed.
Lemma lem4343392 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term673 A B x x' x'' s' s t' t) = (term674 A B x x' x'' s' s t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343391 A B x x' x'' x''' s' s t' t)). Qed.
Lemma lem4343393 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343394 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term662 A B x x' x'' s' s t' t) = (term675 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343393 B) (@lem4343392 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343395 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term661 A B x x' x'' s' s t' t) = (term662 A B x x' x'' s' s t' t)) = ((term657 A B x x' x'' s' s t' t) = (term675 A B x x' x'' s' s t' t)).
Proof. exact (MK_COMB (@lem4343386 A B x x' x'' s' s t' t) (@lem4343394 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343396 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term657 A B x x' x'' s' s t' t) = (term675 A B x x' x'' s' s t' t).
Proof. exact (EQ_MP (@lem4343395 A B x x' x'' s' s t' t) (@lem4343376 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343397 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term659 A B x x' s' s t' t) = (term676 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343396 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343398 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343399 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term660 A B x x' s' s t' t) = (term677 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343398 A) (@lem4343397 A B x x' s' s t' t)). Qed.
Lemma lem4343400 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term642 A B x x' s' s t' t) = (term677 A B x x' s' s t' t).
Proof. exact (TRANS (@lem4343372 A B x x' s' s t' t) (@lem4343399 A B x x' s' s t' t)). Qed.
Lemma lem4343401 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term644 A B x s' s t' t) = (term678 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343400 A B x x' s' s t' t)). Qed.
Lemma lem4343402 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343403 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term645 A B x s' s t' t) = (term679 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343402 B) (@lem4343401 A B x s' s t' t)). Qed.
Lemma lem4343404 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term627 A B x s' s t' t) = (term679 A B x s' s t' t).
Proof. exact (TRANS (@lem4343348 A B x s' s t' t) (@lem4343403 A B x s' s t' t)). Qed.
Lemma lem4343405 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term629 A B s' s t' t) = (term680 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343404 A B x s' s t' t)). Qed.
Lemma lem4343406 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343407 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term630 A B s' s t' t) = (term681 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343406 A) (@lem4343405 A B s' s t' t)). Qed.
Lemma lem4343408 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term615 A B s' s t' t) = (term681 A B s' s t' t).
Proof. exact (TRANS (@lem4343324 A B s' s t' t) (@lem4343407 A B s' s t' t)). Qed.
Lemma lem4343409 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term225 A B s' s t' t) = (term681 A B s' s t' t).
Proof. exact (TRANS (@lem4343300 A B s' s t' t) (@lem4343408 A B s' s t' t)). Qed.
Lemma lem4343410 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term233 A B s' s t' t) = (term682 A B s' s t' t).
Proof. exact (MK_COMB (@lem4342804 A B s' s t' t) (@lem4343409 A B s' s t' t)). Qed.
Lemma lem4343412 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343413 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (@lem4343412 A P Q). Qed.
Lemma lem4343414 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term683 A B s' s t' t) = (term684 A B s' s t' t).
Proof. exact (@lem4343413 A (term444 A B s' s t' t) (term680 A B s' s t' t)). Qed.
Lemma lem4343415 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term685 A B s' s t' t x) = (term443 A B x s' s t' t).
Proof. exact (eq_refl (term685 A B s' s t' t x)). Qed.
Lemma lem4343416 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term686 A B s' s t' t) = (term444 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343415 A B x s' s t' t)). Qed.
Lemma lem4343417 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343418 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term687 A B s' s t' t) = (term445 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343417 A) (@lem4343416 A B s' s t' t)). Qed.
Lemma lem4343419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343420 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term688 A B s' s t' t) = (term446 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343419) (@lem4343418 A B s' s t' t)). Qed.
Lemma lem4343421 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term689 A B s' s t' t x) = (term679 A B x s' s t' t).
Proof. exact (eq_refl (term689 A B s' s t' t x)). Qed.
Lemma lem4343422 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term690 A B s' s t' t) = (term680 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343421 A B x s' s t' t)). Qed.
Lemma lem4343423 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343424 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term691 A B s' s t' t) = (term681 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343423 A) (@lem4343422 A B s' s t' t)). Qed.
Lemma lem4343425 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term683 A B s' s t' t) = (term682 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343420 A B s' s t' t) (@lem4343424 A B s' s t' t)). Qed.
Lemma lem4343426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343427 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term692 A B s' s t' t) = (term693 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343426) (@lem4343425 A B s' s t' t)). Qed.
Lemma lem4343428 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term685 A B s' s t' t x) = (term443 A B x s' s t' t).
Proof. exact (eq_refl (term685 A B s' s t' t x)). Qed.
Lemma lem4343429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343430 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term694 A B s' s t' t x) = (term695 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343429) (@lem4343428 A B x s' s t' t)). Qed.
Lemma lem4343431 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term689 A B s' s t' t x) = (term679 A B x s' s t' t).
Proof. exact (eq_refl (term689 A B s' s t' t x)). Qed.
Lemma lem4343432 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term696 A B s' s t' t x) = (term697 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343430 A B x s' s t' t) (@lem4343431 A B x s' s t' t)). Qed.
Lemma lem4343433 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term698 A B s' s t' t) = (term699 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343432 A B x s' s t' t)). Qed.
Lemma lem4343434 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343435 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term684 A B s' s t' t) = (term700 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343434 A) (@lem4343433 A B s' s t' t)). Qed.
Lemma lem4343436 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term683 A B s' s t' t) = (term684 A B s' s t' t)) = ((term682 A B s' s t' t) = (term700 A B s' s t' t)).
Proof. exact (MK_COMB (@lem4343427 A B s' s t' t) (@lem4343435 A B s' s t' t)). Qed.
Lemma lem4343437 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term682 A B s' s t' t) = (term700 A B s' s t' t).
Proof. exact (EQ_MP (@lem4343436 A B s' s t' t) (@lem4343414 A B s' s t' t)). Qed.
Lemma lem4343439 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343440 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term246 B P Q) = (term247 B P Q).
Proof. exact (@lem4343439 B P Q). Qed.
Lemma lem4343441 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term701 A B x s' s t' t) = (term702 A B x s' s t' t).
Proof. exact (@lem4343440 B (term442 A B x s' s t' t) (term678 A B x s' s t' t)). Qed.
Lemma lem4343442 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term703 A B x s' s t' t x') = (term441 A B x x' s' s t' t).
Proof. exact (eq_refl (term703 A B x s' s t' t x')). Qed.
Lemma lem4343443 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term704 A B x s' s t' t) = (term442 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343442 A B x x' s' s t' t)). Qed.
Lemma lem4343444 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343445 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term705 A B x s' s t' t) = (term443 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343444 B) (@lem4343443 A B x s' s t' t)). Qed.
Lemma lem4343446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343447 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term706 A B x s' s t' t) = (term695 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343446) (@lem4343445 A B x s' s t' t)). Qed.
Lemma lem4343448 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term707 A B x s' s t' t x') = (term677 A B x x' s' s t' t).
Proof. exact (eq_refl (term707 A B x s' s t' t x')). Qed.
Lemma lem4343449 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term708 A B x s' s t' t) = (term678 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343448 A B x x' s' s t' t)). Qed.
Lemma lem4343450 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343451 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term709 A B x s' s t' t) = (term679 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343450 B) (@lem4343449 A B x s' s t' t)). Qed.
Lemma lem4343452 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term701 A B x s' s t' t) = (term697 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343447 A B x s' s t' t) (@lem4343451 A B x s' s t' t)). Qed.
Lemma lem4343453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343454 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term710 A B x s' s t' t) = (term711 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343453) (@lem4343452 A B x s' s t' t)). Qed.
Lemma lem4343455 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term703 A B x s' s t' t x') = (term441 A B x x' s' s t' t).
Proof. exact (eq_refl (term703 A B x s' s t' t x')). Qed.
Lemma lem4343456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343457 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term712 A B x s' s t' t x') = (term713 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343456) (@lem4343455 A B x x' s' s t' t)). Qed.
Lemma lem4343458 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term707 A B x s' s t' t x') = (term677 A B x x' s' s t' t).
Proof. exact (eq_refl (term707 A B x s' s t' t x')). Qed.
Lemma lem4343459 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term714 A B x s' s t' t x') = (term715 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343457 A B x x' s' s t' t) (@lem4343458 A B x x' s' s t' t)). Qed.
Lemma lem4343460 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term716 A B x s' s t' t) = (term717 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343459 A B x x' s' s t' t)). Qed.
Lemma lem4343461 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343462 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term702 A B x s' s t' t) = (term718 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343461 B) (@lem4343460 A B x s' s t' t)). Qed.
Lemma lem4343463 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term701 A B x s' s t' t) = (term702 A B x s' s t' t)) = ((term697 A B x s' s t' t) = (term718 A B x s' s t' t)).
Proof. exact (MK_COMB (@lem4343454 A B x s' s t' t) (@lem4343462 A B x s' s t' t)). Qed.
Lemma lem4343464 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term697 A B x s' s t' t) = (term718 A B x s' s t' t).
Proof. exact (EQ_MP (@lem4343463 A B x s' s t' t) (@lem4343441 A B x s' s t' t)). Qed.
Lemma lem4343466 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343467 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (@lem4343466 A P Q). Qed.
Lemma lem4343468 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term719 A B x x' s' s t' t) = (term720 A B x x' s' s t' t).
Proof. exact (@lem4343467 A (term440 A B x x' s' s t' t) (term676 A B x x' s' s t' t)). Qed.
Lemma lem4343469 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term721 A B x x' s' s t' t x'') = (term439 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term721 A B x x' s' s t' t x'')). Qed.
Lemma lem4343470 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term722 A B x x' s' s t' t) = (term440 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343469 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343471 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343472 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term723 A B x x' s' s t' t) = (term441 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343471 A) (@lem4343470 A B x x' s' s t' t)). Qed.
Lemma lem4343473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343474 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term724 A B x x' s' s t' t) = (term713 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343473) (@lem4343472 A B x x' s' s t' t)). Qed.
Lemma lem4343475 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term725 A B x x' s' s t' t x'') = (term675 A B x x' x'' s' s t' t).
Proof. exact (eq_refl (term725 A B x x' s' s t' t x'')). Qed.
Lemma lem4343476 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term726 A B x x' s' s t' t) = (term676 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343475 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343477 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343478 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term727 A B x x' s' s t' t) = (term677 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343477 A) (@lem4343476 A B x x' s' s t' t)). Qed.
Lemma lem4343479 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term719 A B x x' s' s t' t) = (term715 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343474 A B x x' s' s t' t) (@lem4343478 A B x x' s' s t' t)). Qed.
Lemma lem4343480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343481 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term728 A B x x' s' s t' t) = (term729 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343480) (@lem4343479 A B x x' s' s t' t)). Qed.
Lemma lem4343482 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term721 A B x x' s' s t' t x'') = (term439 A B x x' s' s x'' t' t).
Proof. exact (eq_refl (term721 A B x x' s' s t' t x'')). Qed.
Lemma lem4343483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343484 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term730 A B x x' s' s t' t x'') = (term731 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343483) (@lem4343482 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343485 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term725 A B x x' s' s t' t x'') = (term675 A B x x' x'' s' s t' t).
Proof. exact (eq_refl (term725 A B x x' s' s t' t x'')). Qed.
Lemma lem4343486 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term732 A B x x' s' s t' t x'') = (term733 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343484 A B x x' s' s x'' t' t) (@lem4343485 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343487 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term734 A B x x' s' s t' t) = (term735 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343486 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343488 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343489 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term720 A B x x' s' s t' t) = (term736 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343488 A) (@lem4343487 A B x x' s' s t' t)). Qed.
Lemma lem4343490 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term719 A B x x' s' s t' t) = (term720 A B x x' s' s t' t)) = ((term715 A B x x' s' s t' t) = (term736 A B x x' s' s t' t)).
Proof. exact (MK_COMB (@lem4343481 A B x x' s' s t' t) (@lem4343489 A B x x' s' s t' t)). Qed.
Lemma lem4343491 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term715 A B x x' s' s t' t) = (term736 A B x x' s' s t' t).
Proof. exact (EQ_MP (@lem4343490 A B x x' s' s t' t) (@lem4343468 A B x x' s' s t' t)). Qed.
Lemma lem4343493 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4343494 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term246 B P Q) = (term247 B P Q).
Proof. exact (@lem4343493 B P Q). Qed.
Lemma lem4343495 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term737 A B x x' x'' s' s t' t) = (term738 A B x x' x'' s' s t' t).
Proof. exact (@lem4343494 B (term438 A B x x' s' s x'' t' t) (term674 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343496 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term739 A B x x' s' s x'' t' t x''') = (term436 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term739 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343497 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term740 A B x x' s' s x'' t' t) = (term438 A B x x' s' s x'' t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343496 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343498 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343499 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term741 A B x x' s' s x'' t' t) = (term439 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343498 B) (@lem4343497 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343501 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) : (term742 A B x x' s' s x'' t' t) = (term731 A B x x' s' s x'' t' t).
Proof. exact (MK_COMB (@lem4343500) (@lem4343499 A B x x' s' s x'' t' t)). Qed.
Lemma lem4343502 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term743 A B x x' x'' s' s t' t x''') = (term672 A B x x' x'' x''' s' s t' t).
Proof. exact (eq_refl (term743 A B x x' x'' s' s t' t x''')). Qed.
Lemma lem4343503 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term744 A B x x' x'' s' s t' t) = (term674 A B x x' x'' s' s t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343502 A B x x' x'' x''' s' s t' t)). Qed.
Lemma lem4343504 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343505 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term745 A B x x' x'' s' s t' t) = (term675 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343504 B) (@lem4343503 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343506 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term737 A B x x' x'' s' s t' t) = (term733 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343501 A B x x' s' s x'' t' t) (@lem4343505 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4343508 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term746 A B x x' x'' s' s t' t) = (term747 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343507) (@lem4343506 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343509 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term739 A B x x' s' s x'' t' t x''') = (term436 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term739 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343511 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term748 A B x x' s' s x'' t' t x''') = (term749 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4343510) (@lem4343509 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343512 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term743 A B x x' x'' s' s t' t x''') = (term672 A B x x' x'' x''' s' s t' t).
Proof. exact (eq_refl (term743 A B x x' x'' s' s t' t x''')). Qed.
Lemma lem4343513 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term750 A B x x' x'' s' s t' t x''') = (term751 A B x x' x'' x''' s' s t' t).
Proof. exact (MK_COMB (@lem4343511 A B x x' s' s x'' t' t x''') (@lem4343512 A B x x' x'' x''' s' s t' t)). Qed.
Lemma lem4343514 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term752 A B x x' x'' s' s t' t) = (term753 A B x x' x'' s' s t' t).
Proof. exact (fun_ext (fun x''' : B => @lem4343513 A B x x' x'' x''' s' s t' t)). Qed.
Lemma lem4343515 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343516 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term738 A B x x' x'' s' s t' t) = (term754 A B x x' x'' s' s t' t).
Proof. exact (MK_COMB (@lem4343515 B) (@lem4343514 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343517 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : ((term737 A B x x' x'' s' s t' t) = (term738 A B x x' x'' s' s t' t)) = ((term733 A B x x' x'' s' s t' t) = (term754 A B x x' x'' s' s t' t)).
Proof. exact (MK_COMB (@lem4343508 A B x x' x'' s' s t' t) (@lem4343516 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343518 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term733 A B x x' x'' s' s t' t) = (term754 A B x x' x'' s' s t' t).
Proof. exact (EQ_MP (@lem4343517 A B x x' x'' s' s t' t) (@lem4343495 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343519 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term735 A B x x' s' s t' t) = (term755 A B x x' s' s t' t).
Proof. exact (fun_ext (fun x'' : A => @lem4343518 A B x x' x'' s' s t' t)). Qed.
Lemma lem4343520 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343521 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term736 A B x x' s' s t' t) = (term756 A B x x' s' s t' t).
Proof. exact (MK_COMB (@lem4343520 A) (@lem4343519 A B x x' s' s t' t)). Qed.
Lemma lem4343522 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term715 A B x x' s' s t' t) = (term756 A B x x' s' s t' t).
Proof. exact (TRANS (@lem4343491 A B x x' s' s t' t) (@lem4343521 A B x x' s' s t' t)). Qed.
Lemma lem4343523 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term717 A B x s' s t' t) = (term757 A B x s' s t' t).
Proof. exact (fun_ext (fun x' : B => @lem4343522 A B x x' s' s t' t)). Qed.
Lemma lem4343524 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4343525 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term718 A B x s' s t' t) = (term758 A B x s' s t' t).
Proof. exact (MK_COMB (@lem4343524 B) (@lem4343523 A B x s' s t' t)). Qed.
Lemma lem4343526 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term697 A B x s' s t' t) = (term758 A B x s' s t' t).
Proof. exact (TRANS (@lem4343464 A B x s' s t' t) (@lem4343525 A B x s' s t' t)). Qed.
Lemma lem4343527 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term699 A B s' s t' t) = (term759 A B s' s t' t).
Proof. exact (fun_ext (fun x : A => @lem4343526 A B x s' s t' t)). Qed.
Lemma lem4343528 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4343529 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term700 A B s' s t' t) = (term760 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343528 A) (@lem4343527 A B s' s t' t)). Qed.
Lemma lem4343530 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term682 A B s' s t' t) = (term760 A B s' s t' t).
Proof. exact (TRANS (@lem4343437 A B s' s t' t) (@lem4343529 A B s' s t' t)). Qed.
Lemma lem4343532 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term233 A B s' s t' t) = (term760 A B s' s t' t).
Proof. exact (TRANS (@lem4343410 A B s' s t' t) (@lem4343530 A B s' s t' t)). Qed.
Lemma lem4343533 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term150 A B s' s t' t) = (term760 A B s' s t' t).
Proof. exact (TRANS (@lem4341864 A B s' s t' t) (@lem4343532 A B s' s t' t)). Qed.
Lemma lem4343534 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term150 A B s' s t' t) : term760 A B s' s t' t.
Proof. exact (EQ_MP (@lem4343533 A B s' s t' t) (@lem4341389 A B s' s t' t h1)). Qed.
Lemma lem4343535 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term758 A B x s' s t' t) : term758 A B x s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4343536 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term756 A B x x' s' s t' t) : term756 A B x x' s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4343537 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term754 A B x x' x'' s' s t' t) : term754 A B x x' x'' s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4343538 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term751 A B x x' x'' x''' s' s t' t) : term751 A B x x' x'' x''' s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4343549 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4343550 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4343549 B t' t x)). Qed.
Lemma lem4343551 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343552 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4343551 B) (@lem4343550 B t' t)). Qed.
Lemma lem4343563 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4343564 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4343563 B t t' x)). Qed.
Lemma lem4343565 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343566 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4343565 B) (@lem4343564 B t t')). Qed.
Lemma lem4343567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343568 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term178 B t t') = (term178 B t t').
Proof. exact (MK_COMB (@lem4343567) (@lem4343566 B t t')). Qed.
Lemma lem4343569 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term208 B t' t) = (term208 B t' t).
Proof. exact (MK_COMB (@lem4343568 B t t') (@lem4343552 B t' t)). Qed.
Lemma lem4343580 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4343581 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4343580 A s' s x)). Qed.
Lemma lem4343582 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343583 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4343582 A) (@lem4343581 A s' s)). Qed.
Lemma lem4343594 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4343595 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4343594 A s s' x)). Qed.
Lemma lem4343596 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343597 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4343596 A) (@lem4343595 A s s')). Qed.
Lemma lem4343598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343599 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term178 A s s') = (term178 A s s').
Proof. exact (MK_COMB (@lem4343598) (@lem4343597 A s s')). Qed.
Lemma lem4343600 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term208 A s' s) = (term208 A s' s).
Proof. exact (MK_COMB (@lem4343599 A s s') (@lem4343583 A s' s)). Qed.
Lemma lem4343601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343602 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term214 A s' s) = (term214 A s' s).
Proof. exact (MK_COMB (@lem4343601) (@lem4343600 A s' s)). Qed.
Lemma lem4343603 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term215 A B s' s t' t) = (term215 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343602 A s' s) (@lem4343569 B t' t)). Qed.
Lemma lem4343608 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4343609 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4343608 B t' x)). Qed.
Lemma lem4343610 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343611 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4343610 B) (@lem4343609 B t')). Qed.
Lemma lem4343616 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4343617 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4343616 A s' x)). Qed.
Lemma lem4343618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343619 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4343618 A) (@lem4343617 A s')). Qed.
Lemma lem4343620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343621 {A : Type'} (s' : A -> Prop) : (term112 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4343620) (@lem4343619 A s')). Qed.
Lemma lem4343622 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) : (term125 A B s' t') = (term125 A B s' t').
Proof. exact (MK_COMB (@lem4343621 A s') (@lem4343611 B t')). Qed.
Lemma lem4343627 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4343628 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4343627 B t x)). Qed.
Lemma lem4343629 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343630 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4343629 B) (@lem4343628 B t)). Qed.
Lemma lem4343635 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4343636 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4343635 A s x)). Qed.
Lemma lem4343637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343638 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4343637 A) (@lem4343636 A s)). Qed.
Lemma lem4343639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343640 {A : Type'} (s : A -> Prop) : (term112 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4343639) (@lem4343638 A s)). Qed.
Lemma lem4343641 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term125 A B s t) = (term125 A B s t).
Proof. exact (MK_COMB (@lem4343640 A s) (@lem4343630 B t)). Qed.
Lemma lem4343642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343643 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term126 A B s t) = (term126 A B s t).
Proof. exact (MK_COMB (@lem4343642) (@lem4343641 A B s t)). Qed.
Lemma lem4343644 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term127 A B s t s' t') = (term127 A B s t s' t').
Proof. exact (MK_COMB (@lem4343643 A B s t) (@lem4343622 A B s' t')). Qed.
Lemma lem4343645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343646 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) : (term128 A B s t s' t') = (term128 A B s t s' t').
Proof. exact (MK_COMB (@lem4343645) (@lem4343644 A B s t s' t')). Qed.
Lemma lem4343647 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term221 A B s' s t' t) = (term221 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343646 A B s t s' t') (@lem4343603 A B s' s t' t)). Qed.
Lemma lem4343726 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term670 A B x x' s' s x'' t' t x''') = (term670 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term670 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343727 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term672 A B x x' x'' x''' s' s t' t) = (term672 A B x x' x'' x''' s' s t' t).
Proof. exact (MK_COMB (@lem4343726 A B x x' s' s x'' t' t x''') (@lem4343647 A B s' s t' t)). Qed.
Lemma lem4343804 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term381 A B x x' s' s x'' t' t x''') = (term381 A B x x' s' s x'' t' t x''').
Proof. exact (eq_refl (term381 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343815 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4343816 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4343815 B t' t x)). Qed.
Lemma lem4343817 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343818 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4343817 B) (@lem4343816 B t' t)). Qed.
Lemma lem4343829 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4343830 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4343829 A s' s x)). Qed.
Lemma lem4343831 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343832 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4343831 A) (@lem4343830 A s' s)). Qed.
Lemma lem4343833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343834 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term178 A s' s) = (term178 A s' s).
Proof. exact (MK_COMB (@lem4343833) (@lem4343832 A s' s)). Qed.
Lemma lem4343835 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term179 A B s' s t' t) = (term179 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343834 A s' s) (@lem4343818 B t' t)). Qed.
Lemma lem4343840 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4343841 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4343840 B t' x)). Qed.
Lemma lem4343842 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343843 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4343842 B) (@lem4343841 B t')). Qed.
Lemma lem4343844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343845 {B : Type'} (t' : B -> Prop) : (term112 B t') = (term112 B t').
Proof. exact (MK_COMB (@lem4343844) (@lem4343843 B t')). Qed.
Lemma lem4343846 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term185 A B s' s t' t) = (term185 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343845 B t') (@lem4343835 A B s' s t' t)). Qed.
Lemma lem4343851 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4343852 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4343851 A s' x)). Qed.
Lemma lem4343853 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343854 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4343853 A) (@lem4343852 A s')). Qed.
Lemma lem4343855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343856 {A : Type'} (s' : A -> Prop) : (term112 A s') = (term112 A s').
Proof. exact (MK_COMB (@lem4343855) (@lem4343854 A s')). Qed.
Lemma lem4343857 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term189 A B s' s t' t) = (term189 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343856 A s') (@lem4343846 A B s' s t' t)). Qed.
Lemma lem4343868 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4343869 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4343868 B t t' x)). Qed.
Lemma lem4343870 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343871 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4343870 B) (@lem4343869 B t t')). Qed.
Lemma lem4343882 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4343883 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4343882 A s s' x)). Qed.
Lemma lem4343884 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343885 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4343884 A) (@lem4343883 A s s')). Qed.
Lemma lem4343886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343887 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term178 A s s') = (term178 A s s').
Proof. exact (MK_COMB (@lem4343886) (@lem4343885 A s s')). Qed.
Lemma lem4343888 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term179 A B s s' t t') = (term179 A B s s' t t').
Proof. exact (MK_COMB (@lem4343887 A s s') (@lem4343871 B t t')). Qed.
Lemma lem4343893 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4343894 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4343893 B t x)). Qed.
Lemma lem4343895 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4343896 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4343895 B) (@lem4343894 B t)). Qed.
Lemma lem4343897 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343898 {B : Type'} (t : B -> Prop) : (term112 B t) = (term112 B t).
Proof. exact (MK_COMB (@lem4343897) (@lem4343896 B t)). Qed.
Lemma lem4343899 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term185 A B s s' t t') = (term185 A B s s' t t').
Proof. exact (MK_COMB (@lem4343898 B t) (@lem4343888 A B s s' t t')). Qed.
Lemma lem4343904 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4343905 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4343904 A s x)). Qed.
Lemma lem4343906 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4343907 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4343906 A) (@lem4343905 A s)). Qed.
Lemma lem4343908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343909 {A : Type'} (s : A -> Prop) : (term112 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem4343908) (@lem4343907 A s)). Qed.
Lemma lem4343910 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term189 A B s s' t t') = (term189 A B s s' t t').
Proof. exact (MK_COMB (@lem4343909 A s) (@lem4343899 A B s s' t t')). Qed.
Lemma lem4343911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343912 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) : (term195 A B s s' t t') = (term195 A B s s' t t').
Proof. exact (MK_COMB (@lem4343911) (@lem4343910 A B s s' t t')). Qed.
Lemma lem4343913 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term196 A B s' s t' t) = (term196 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343912 A B s s' t t') (@lem4343857 A B s' s t' t)). Qed.
Lemma lem4343914 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4343915 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term227 A B s' s t' t) = (term227 A B s' s t' t).
Proof. exact (MK_COMB (@lem4343914) (@lem4343913 A B s' s t' t)). Qed.
Lemma lem4343916 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term436 A B x x' s' s x'' t' t x''') = (term436 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4343915 A B s' s t' t) (@lem4343804 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4343918 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) : (term749 A B x x' s' s x'' t' t x''') = (term749 A B x x' s' s x'' t' t x''').
Proof. exact (MK_COMB (@lem4343917) (@lem4343916 A B x x' s' s x'' t' t x''')). Qed.
Lemma lem4343919 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term751 A B x x' x'' x''' s' s t' t) = (term751 A B x x' x'' x''' s' s t' t).
Proof. exact (MK_COMB (@lem4343918 A B x x' s' s x'' t' t x''') (@lem4343727 A B x x' x'' x''' s' s t' t)). Qed.
Lemma lem4343920 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term751 A B x x' x'' x''' s' s t' t) : term751 A B x x' x'' x''' s' s t' t.
Proof. exact (EQ_MP (@lem4343919 A B x x' x'' x''' s' s t' t) (@lem4343538 A B x x' x'' x''' s' s t' t h1)). Qed.
Lemma lem4343921 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : term436 A B x x' s' s x'' t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4343922 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term672 A B x x' x'' x''' s' s t' t) : term672 A B x x' x'' x''' s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4343923 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : term381 A B x x' s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4343921 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4343924 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : term196 A B s' s t' t.
Proof. exact (proj1 (@lem4343921 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4343925 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : term324 A B s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4343923 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4343926 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : term276 A B s t s' x t' x'.
Proof. exact (proj1 (@lem4343923 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4343927 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : term189 A B s' s t' t.
Proof. exact (proj2 (@lem4343924 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4343928 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : term189 A B s s' t t'.
Proof. exact (proj1 (@lem4343924 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4343929 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (h1). Qed.
Lemma lem4343930 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term185 A B s' s t' t) : term185 A B s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4343931 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (h1). Qed.
Lemma lem4343932 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term185 A B s s' t t') : term185 A B s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4343933 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4343934 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4343935 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4343939 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4343947 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4343948 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4343957 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4343958 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4343965 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4343966 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4343971 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (h1). Qed.
Lemma lem4343972 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term179 A B s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4343973 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4343974 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4343979 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4343980 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4343987 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4343988 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4343993 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4343997 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344005 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344006 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344011 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (proj2 (@lem4343972 A B s s' t t' h1)). Qed.
Lemma lem4344012 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (proj1 (@lem4343972 A B s s' t t' h1)). Qed.
Lemma lem4344013 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344014 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344015 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344016 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term162 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344020 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344028 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344033 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344038 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344045 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344046 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344051 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (h1). Qed.
Lemma lem4344052 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term179 A B s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4344053 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (h1). Qed.
Lemma lem4344054 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term185 A B s s' t t') : term185 A B s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4344055 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344056 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344057 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344061 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344069 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344070 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344079 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344080 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344087 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344088 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344093 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (h1). Qed.
Lemma lem4344094 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term179 A B s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4344095 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344096 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344101 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344102 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344109 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344110 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344115 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344119 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344127 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344128 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344133 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (proj2 (@lem4344094 A B s s' t t' h1)). Qed.
Lemma lem4344134 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (proj1 (@lem4344094 A B s s' t t' h1)). Qed.
Lemma lem4344135 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344136 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344137 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344142 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344149 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344150 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344155 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344156 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term162 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344160 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344168 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344173 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 B t' t.
Proof. exact (proj2 (@lem4344052 A B s' s t' t h1)). Qed.
Lemma lem4344174 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 A s' s.
Proof. exact (proj1 (@lem4344052 A B s' s t' t h1)). Qed.
Lemma lem4344175 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (h1). Qed.
Lemma lem4344176 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term185 A B s s' t t') : term185 A B s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4344177 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344178 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344179 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344180 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term162 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344183 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344191 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344198 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term162 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344201 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344202 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344209 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344215 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (h1). Qed.
Lemma lem4344216 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term179 A B s s' t t'.
Proof. exact (h1). Qed.
Lemma lem4344217 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344218 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344220 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term162 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344223 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344224 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term267 A B s' x t' x'.
Proof. exact (h1). Qed.
Lemma lem4344231 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344237 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344238 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term162 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344241 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344249 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term267 A B s x t x'.
Proof. exact (h1). Qed.
Lemma lem4344255 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (proj2 (@lem4344216 A B s s' t t' h1)). Qed.
Lemma lem4344256 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (proj1 (@lem4344216 A B s s' t t' h1)). Qed.
Lemma lem4344257 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term294 A s' s x'') : term294 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344258 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term294 B t' t x''') : term294 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344259 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344260 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term162 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344277 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344278 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term162 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344295 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term672 A B x x' x'' x''' s' s t' t) : term221 A B s' s t' t.
Proof. exact (proj2 (@lem4343922 A B x x' x'' x''' s' s t' t h1)). Qed.
Lemma lem4344296 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term672 A B x x' x'' x''' s' s t' t) : term604 A B x x' s' s x'' t' t x'''.
Proof. exact (proj1 (@lem4343922 A B x x' x'' x''' s' s t' t h1)). Qed.
Lemma lem4344297 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) (h1 : term127 A B s t s' t') : term127 A B s t s' t'.
Proof. exact (h1). Qed.
Lemma lem4344298 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term215 A B s' s t' t.
Proof. exact (h1). Qed.
Lemma lem4344299 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) (h1 : term127 A B s t s' t') : term125 A B s' t'.
Proof. exact (proj2 (@lem4344297 A B s t s' t' h1)). Qed.
Lemma lem4344300 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (t' : B -> Prop) (h1 : term127 A B s t s' t') : term125 A B s t.
Proof. exact (proj1 (@lem4344297 A B s t s' t' h1)). Qed.
Lemma lem4344301 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (h1). Qed.
Lemma lem4344302 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (h1). Qed.
Lemma lem4344303 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (h1). Qed.
Lemma lem4344304 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (h1). Qed.
Lemma lem4344305 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term535 A B x x' s s' x'' t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344306 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term535 A B x x' s' s x'' t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344307 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term491 A B x' s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344305 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344309 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term461 A B s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344307 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344311 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344317 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term491 A B x' s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344306 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344319 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term461 A B s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344317 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344321 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term162 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344327 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term535 A B x x' s s' x'' t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344328 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term535 A B x x' s' s x'' t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344329 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term491 A B x' s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344327 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344331 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term461 A B s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344329 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344334 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344339 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term491 A B x' s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344328 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344341 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term461 A B s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344339 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344343 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term162 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344349 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (h1). Qed.
Lemma lem4344350 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (h1). Qed.
Lemma lem4344351 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term535 A B x x' s s' x'' t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344352 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term535 A B x x' s' s x'' t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344353 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term491 A B x' s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344351 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344355 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term461 A B s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344353 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344357 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344363 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term491 A B x' s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344352 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344365 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term461 A B s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344363 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344368 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term162 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344373 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term535 A B x x' s s' x'' t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344374 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term535 A B x x' s' s x'' t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344375 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term491 A B x' s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344373 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344377 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term461 A B s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344375 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344380 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344385 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term491 A B x' s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344374 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344387 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term461 A B s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344385 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344390 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term162 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344395 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term208 B t' t.
Proof. exact (proj2 (@lem4344298 A B s' s t' t h1)). Qed.
Lemma lem4344396 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term208 A s' s.
Proof. exact (proj1 (@lem4344298 A B s' s t' t h1)). Qed.
Lemma lem4344397 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 B t' t.
Proof. exact (proj2 (@lem4344395 A B s' s t' t h1)). Qed.
Lemma lem4344398 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 B t t'.
Proof. exact (proj1 (@lem4344395 A B s' s t' t h1)). Qed.
Lemma lem4344399 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 A s' s.
Proof. exact (proj2 (@lem4344396 A B s' s t' t h1)). Qed.
Lemma lem4344400 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 A s s'.
Proof. exact (proj1 (@lem4344396 A B s' s t' t h1)). Qed.
Lemma lem4344401 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term535 A B x x' s s' x'' t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344402 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term535 A B x x' s' s x'' t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344403 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term491 A B x' s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344401 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344405 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term461 A B s s' x'' t t' x'''.
Proof. exact (proj2 (@lem4344403 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4344407 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term162 A s s' x''.
Proof. exact (h1). Qed.
Lemma lem4344408 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term162 B t t' x'''.
Proof. exact (h1). Qed.
Lemma lem4344413 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term491 A B x' s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344402 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344415 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term461 A B s' s x'' t' t x'''.
Proof. exact (proj2 (@lem4344413 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4344417 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term162 A s' s x''.
Proof. exact (h1). Qed.
Lemma lem4344418 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term162 B t' t x'''.
Proof. exact (h1). Qed.
Lemma lem4344431 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4344432 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4344431 A s x)). Qed.
Lemma lem4344433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344435 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4344433 A) (@lem4344432 A s)). Qed.
Lemma lem4344436 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4344435 A s) (@lem4343931 A s h1)). Qed.
Lemma lem4344461 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4344462 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4344461 A s x)). Qed.
Lemma lem4344463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344465 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4344463 A) (@lem4344462 A s)). Qed.
Lemma lem4344466 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4344465 A s) (@lem4343931 A s h1)). Qed.
Lemma lem4344491 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4344492 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4344491 A s x)). Qed.
Lemma lem4344493 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344495 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4344493 A) (@lem4344492 A s)). Qed.
Lemma lem4344496 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4344495 A s) (@lem4343931 A s h1)). Qed.
Lemma lem4344514 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4344515 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4344514 A s' x)). Qed.
Lemma lem4344516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344518 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4344516 A) (@lem4344515 A s')). Qed.
Lemma lem4344519 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4344518 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4344551 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4344552 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4344551 A s x)). Qed.
Lemma lem4344553 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344555 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4344553 A) (@lem4344552 A s)). Qed.
Lemma lem4344556 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4344555 A s) (@lem4343931 A s h1)). Qed.
Lemma lem4344574 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4344575 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4344574 A s' x)). Qed.
Lemma lem4344576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344578 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4344576 A) (@lem4344575 A s')). Qed.
Lemma lem4344579 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4344578 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4344611 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4344612 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4344611 A s x)). Qed.
Lemma lem4344613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344615 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4344613 A) (@lem4344612 A s)). Qed.
Lemma lem4344616 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4344615 A s) (@lem4343931 A s h1)). Qed.
Lemma lem4344634 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4344635 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4344634 A s' x)). Qed.
Lemma lem4344636 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344638 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4344636 A) (@lem4344635 A s')). Qed.
Lemma lem4344639 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4344638 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4344671 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4344672 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4344671 B t x)). Qed.
Lemma lem4344673 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4344675 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4344673 B) (@lem4344672 B t)). Qed.
Lemma lem4344676 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4344675 B t) (@lem4343971 B t h1)). Qed.
Lemma lem4344694 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4344695 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4344694 A s' x)). Qed.
Lemma lem4344696 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344698 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4344696 A) (@lem4344695 A s')). Qed.
Lemma lem4344699 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4344698 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4344731 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4344732 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4344731 B t x)). Qed.
Lemma lem4344733 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4344735 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4344733 B) (@lem4344732 B t)). Qed.
Lemma lem4344736 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4344735 B t) (@lem4343971 B t h1)). Qed.
Lemma lem4344754 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4344755 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4344754 A s' x)). Qed.
Lemma lem4344756 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344758 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4344756 A) (@lem4344755 A s')). Qed.
Lemma lem4344759 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4344758 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4344791 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4344792 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4344791 B t x)). Qed.
Lemma lem4344793 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4344795 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4344793 B) (@lem4344792 B t)). Qed.
Lemma lem4344796 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4344795 B t) (@lem4343971 B t h1)). Qed.
Lemma lem4344821 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4344822 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4344821 B t x)). Qed.
Lemma lem4344823 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4344825 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4344823 B) (@lem4344822 B t)). Qed.
Lemma lem4344826 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4344825 B t) (@lem4343971 B t h1)). Qed.
Lemma lem4344851 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4344852 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4344851 B t x)). Qed.
Lemma lem4344853 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4344855 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4344853 B) (@lem4344852 B t)). Qed.
Lemma lem4344856 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4344855 B t) (@lem4343971 B t h1)). Qed.
Lemma lem4344874 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4344875 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4344874 A s' x)). Qed.
Lemma lem4344876 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344878 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4344876 A) (@lem4344875 A s')). Qed.
Lemma lem4344879 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4344878 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4344917 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4344918 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4344917 A s s' x)). Qed.
Lemma lem4344919 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344921 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4344919 A) (@lem4344918 A s s')). Qed.
Lemma lem4344922 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (EQ_MP (@lem4344921 A s s') (@lem4344012 A B s s' t t' h1)). Qed.
Lemma lem4344953 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4344954 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4344953 A s' x)). Qed.
Lemma lem4344955 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4344957 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4344955 A) (@lem4344954 A s')). Qed.
Lemma lem4344958 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4344957 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4345002 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4345003 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4345002 A s' x)). Qed.
Lemma lem4345004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345006 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4345004 A) (@lem4345003 A s')). Qed.
Lemma lem4345007 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4345006 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4345051 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4345052 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4345051 A s' x)). Qed.
Lemma lem4345053 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345055 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4345053 A) (@lem4345052 A s')). Qed.
Lemma lem4345056 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4345055 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4345126 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4345127 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4345126 B t t' x)). Qed.
Lemma lem4345128 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345130 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4345128 B) (@lem4345127 B t t')). Qed.
Lemma lem4345131 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (EQ_MP (@lem4345130 B t t') (@lem4344011 A B s s' t t' h1)). Qed.
Lemma lem4345149 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4345150 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4345149 A s' x)). Qed.
Lemma lem4345151 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345153 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4345151 A) (@lem4345150 A s')). Qed.
Lemma lem4345154 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4345153 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4345198 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4345199 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4345198 A s' x)). Qed.
Lemma lem4345200 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345202 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4345200 A) (@lem4345199 A s')). Qed.
Lemma lem4345203 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4345202 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4345211 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4345212 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4345211 A s s' x)). Qed.
Lemma lem4345213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345215 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4345213 A) (@lem4345212 A s s')). Qed.
Lemma lem4345216 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (EQ_MP (@lem4345215 A s s') (@lem4344012 A B s s' t t' h1)). Qed.
Lemma lem4345247 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4345248 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4345247 A s' x)). Qed.
Lemma lem4345249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345251 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4345249 A) (@lem4345248 A s')). Qed.
Lemma lem4345252 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4345251 A s') (@lem4343929 A s' h1)). Qed.
Lemma lem4345303 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4345304 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4345303 A s x)). Qed.
Lemma lem4345305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345307 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4345305 A) (@lem4345304 A s)). Qed.
Lemma lem4345308 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4345307 A s) (@lem4344053 A s h1)). Qed.
Lemma lem4345333 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4345334 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4345333 A s x)). Qed.
Lemma lem4345335 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345337 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4345335 A) (@lem4345334 A s)). Qed.
Lemma lem4345338 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4345337 A s) (@lem4344053 A s h1)). Qed.
Lemma lem4345363 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4345364 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4345363 A s x)). Qed.
Lemma lem4345365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345367 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4345365 A) (@lem4345364 A s)). Qed.
Lemma lem4345368 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4345367 A s) (@lem4344053 A s h1)). Qed.
Lemma lem4345386 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345387 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345386 B t' x)). Qed.
Lemma lem4345388 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345390 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345388 B) (@lem4345387 B t')). Qed.
Lemma lem4345391 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345390 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345423 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4345424 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4345423 A s x)). Qed.
Lemma lem4345425 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345427 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4345425 A) (@lem4345424 A s)). Qed.
Lemma lem4345428 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4345427 A s) (@lem4344053 A s h1)). Qed.
Lemma lem4345446 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345447 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345446 B t' x)). Qed.
Lemma lem4345448 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345450 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345448 B) (@lem4345447 B t')). Qed.
Lemma lem4345451 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345450 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345483 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4345484 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4345483 A s x)). Qed.
Lemma lem4345485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345487 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4345485 A) (@lem4345484 A s)). Qed.
Lemma lem4345488 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4345487 A s) (@lem4344053 A s h1)). Qed.
Lemma lem4345506 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345507 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345506 B t' x)). Qed.
Lemma lem4345508 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345510 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345508 B) (@lem4345507 B t')). Qed.
Lemma lem4345511 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345510 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345543 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4345544 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4345543 B t x)). Qed.
Lemma lem4345545 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345547 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4345545 B) (@lem4345544 B t)). Qed.
Lemma lem4345548 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4345547 B t) (@lem4344093 B t h1)). Qed.
Lemma lem4345566 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345567 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345566 B t' x)). Qed.
Lemma lem4345568 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345570 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345568 B) (@lem4345567 B t')). Qed.
Lemma lem4345571 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345570 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345603 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4345604 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4345603 B t x)). Qed.
Lemma lem4345605 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345607 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4345605 B) (@lem4345604 B t)). Qed.
Lemma lem4345608 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4345607 B t) (@lem4344093 B t h1)). Qed.
Lemma lem4345626 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345627 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345626 B t' x)). Qed.
Lemma lem4345628 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345630 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345628 B) (@lem4345627 B t')). Qed.
Lemma lem4345631 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345630 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345663 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4345664 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4345663 B t x)). Qed.
Lemma lem4345665 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345667 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4345665 B) (@lem4345664 B t)). Qed.
Lemma lem4345668 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4345667 B t) (@lem4344093 B t h1)). Qed.
Lemma lem4345693 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4345694 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4345693 B t x)). Qed.
Lemma lem4345695 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345697 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4345695 B) (@lem4345694 B t)). Qed.
Lemma lem4345698 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4345697 B t) (@lem4344093 B t h1)). Qed.
Lemma lem4345723 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4345724 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4345723 B t x)). Qed.
Lemma lem4345725 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345727 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4345725 B) (@lem4345724 B t)). Qed.
Lemma lem4345728 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4345727 B t) (@lem4344093 B t h1)). Qed.
Lemma lem4345746 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345747 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345746 B t' x)). Qed.
Lemma lem4345748 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345750 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345748 B) (@lem4345747 B t')). Qed.
Lemma lem4345751 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345750 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345789 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4345790 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4345789 A s s' x)). Qed.
Lemma lem4345791 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4345793 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4345791 A) (@lem4345790 A s s')). Qed.
Lemma lem4345794 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (EQ_MP (@lem4345793 A s s') (@lem4344134 A B s s' t t' h1)). Qed.
Lemma lem4345825 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345826 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345825 B t' x)). Qed.
Lemma lem4345827 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345829 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345827 B) (@lem4345826 B t')). Qed.
Lemma lem4345830 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345829 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345874 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345875 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345874 B t' x)). Qed.
Lemma lem4345876 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345878 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345876 B) (@lem4345875 B t')). Qed.
Lemma lem4345879 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345878 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345900 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4345901 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4345900 B t t' x)). Qed.
Lemma lem4345902 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345904 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4345902 B) (@lem4345901 B t t')). Qed.
Lemma lem4345905 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (EQ_MP (@lem4345904 B t t') (@lem4344133 A B s s' t t' h1)). Qed.
Lemma lem4345923 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4345924 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4345923 B t' x)). Qed.
Lemma lem4345925 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4345927 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4345925 B) (@lem4345924 B t')). Qed.
Lemma lem4345928 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4345927 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4345998 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4345999 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4345998 B t t' x)). Qed.
Lemma lem4346000 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346002 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4346000 B) (@lem4345999 B t t')). Qed.
Lemma lem4346003 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (EQ_MP (@lem4346002 B t t') (@lem4344133 A B s s' t t' h1)). Qed.
Lemma lem4346021 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4346022 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4346021 B t' x)). Qed.
Lemma lem4346023 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346025 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4346023 B) (@lem4346022 B t')). Qed.
Lemma lem4346026 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4346025 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4346070 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4346071 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4346070 B t' x)). Qed.
Lemma lem4346072 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346074 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4346072 B) (@lem4346071 B t')). Qed.
Lemma lem4346075 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4346074 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4346119 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4346120 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4346119 B t' x)). Qed.
Lemma lem4346121 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346123 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4346121 B) (@lem4346120 B t')). Qed.
Lemma lem4346124 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4346123 B t') (@lem4344051 B t' h1)). Qed.
Lemma lem4346194 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4346195 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4346194 A s x)). Qed.
Lemma lem4346196 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346198 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4346196 A) (@lem4346195 A s)). Qed.
Lemma lem4346199 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4346198 A s) (@lem4344175 A s h1)). Qed.
Lemma lem4346243 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4346244 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4346243 A s x)). Qed.
Lemma lem4346245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346247 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4346245 A) (@lem4346244 A s)). Qed.
Lemma lem4346248 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4346247 A s) (@lem4344175 A s h1)). Qed.
Lemma lem4346292 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4346293 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4346292 A s x)). Qed.
Lemma lem4346294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346296 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4346294 A) (@lem4346293 A s)). Qed.
Lemma lem4346297 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4346296 A s) (@lem4344175 A s h1)). Qed.
Lemma lem4346321 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4346322 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4346321 A s' s x)). Qed.
Lemma lem4346323 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346325 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4346323 A) (@lem4346322 A s' s)). Qed.
Lemma lem4346326 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 A s' s.
Proof. exact (EQ_MP (@lem4346325 A s' s) (@lem4344174 A B s' s t' t h1)). Qed.
Lemma lem4346390 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4346391 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4346390 A s x)). Qed.
Lemma lem4346392 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346394 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4346392 A) (@lem4346391 A s)). Qed.
Lemma lem4346395 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4346394 A s) (@lem4344175 A s h1)). Qed.
Lemma lem4346419 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4346420 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4346419 A s' s x)). Qed.
Lemma lem4346421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346423 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4346421 A) (@lem4346420 A s' s)). Qed.
Lemma lem4346424 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 A s' s.
Proof. exact (EQ_MP (@lem4346423 A s' s) (@lem4344174 A B s' s t' t h1)). Qed.
Lemma lem4346439 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4346440 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4346439 A s x)). Qed.
Lemma lem4346441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346443 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4346441 A) (@lem4346440 A s)). Qed.
Lemma lem4346444 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4346443 A s) (@lem4344175 A s h1)). Qed.
Lemma lem4346488 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4346489 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4346488 A s x)). Qed.
Lemma lem4346490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346492 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4346490 A) (@lem4346489 A s)). Qed.
Lemma lem4346493 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4346492 A s) (@lem4344175 A s h1)). Qed.
Lemma lem4346530 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4346531 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4346530 B t' t x)). Qed.
Lemma lem4346532 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346534 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4346532 B) (@lem4346531 B t' t)). Qed.
Lemma lem4346535 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 B t' t.
Proof. exact (EQ_MP (@lem4346534 B t' t) (@lem4344173 A B s' s t' t h1)). Qed.
Lemma lem4346586 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4346587 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4346586 B t x)). Qed.
Lemma lem4346588 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346590 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4346588 B) (@lem4346587 B t)). Qed.
Lemma lem4346591 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4346590 B t) (@lem4344215 B t h1)). Qed.
Lemma lem4346628 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4346629 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4346628 B t' t x)). Qed.
Lemma lem4346630 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346632 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4346630 B) (@lem4346629 B t' t)). Qed.
Lemma lem4346633 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 B t' t.
Proof. exact (EQ_MP (@lem4346632 B t' t) (@lem4344173 A B s' s t' t h1)). Qed.
Lemma lem4346635 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4346636 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4346635 B t x)). Qed.
Lemma lem4346637 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346639 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4346637 B) (@lem4346636 B t)). Qed.
Lemma lem4346640 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4346639 B t) (@lem4344215 B t h1)). Qed.
Lemma lem4346684 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4346685 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4346684 B t x)). Qed.
Lemma lem4346686 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346688 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4346686 B) (@lem4346685 B t)). Qed.
Lemma lem4346689 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4346688 B t) (@lem4344215 B t h1)). Qed.
Lemma lem4346713 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4346714 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4346713 A s' s x)). Qed.
Lemma lem4346715 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346717 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4346715 A) (@lem4346714 A s' s)). Qed.
Lemma lem4346718 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 A s' s.
Proof. exact (EQ_MP (@lem4346717 A s' s) (@lem4344174 A B s' s t' t h1)). Qed.
Lemma lem4346782 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4346783 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4346782 B t x)). Qed.
Lemma lem4346784 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346786 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4346784 B) (@lem4346783 B t)). Qed.
Lemma lem4346787 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4346786 B t) (@lem4344215 B t h1)). Qed.
Lemma lem4346831 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4346832 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4346831 B t x)). Qed.
Lemma lem4346833 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346835 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4346833 B) (@lem4346832 B t)). Qed.
Lemma lem4346836 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4346835 B t) (@lem4344215 B t h1)). Qed.
Lemma lem4346880 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4346881 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4346880 B t x)). Qed.
Lemma lem4346882 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346884 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4346882 B) (@lem4346881 B t)). Qed.
Lemma lem4346885 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4346884 B t) (@lem4344215 B t h1)). Qed.
Lemma lem4346922 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4346923 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4346922 B t' t x)). Qed.
Lemma lem4346924 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4346926 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4346924 B) (@lem4346923 B t' t)). Qed.
Lemma lem4346927 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 B t' t.
Proof. exact (EQ_MP (@lem4346926 B t' t) (@lem4344173 A B s' s t' t h1)). Qed.
Lemma lem4346984 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4346985 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4346984 A s s' x)). Qed.
Lemma lem4346986 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4346988 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4346986 A) (@lem4346985 A s s')). Qed.
Lemma lem4346989 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (EQ_MP (@lem4346988 A s s') (@lem4344256 A B s s' t t' h1)). Qed.
Lemma lem4347052 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4347053 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4347052 A s s' x)). Qed.
Lemma lem4347054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347056 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4347054 A) (@lem4347053 A s s')). Qed.
Lemma lem4347057 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 A s s'.
Proof. exact (EQ_MP (@lem4347056 A s s') (@lem4344256 A B s s' t t' h1)). Qed.
Lemma lem4347094 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4347095 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4347094 A s' s x)). Qed.
Lemma lem4347096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347098 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4347096 A) (@lem4347095 A s' s)). Qed.
Lemma lem4347099 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 A s' s.
Proof. exact (EQ_MP (@lem4347098 A s' s) (@lem4344174 A B s' s t' t h1)). Qed.
Lemma lem4347162 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4347163 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4347162 A s' s x)). Qed.
Lemma lem4347164 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347166 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4347164 A) (@lem4347163 A s' s)). Qed.
Lemma lem4347167 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 A s' s.
Proof. exact (EQ_MP (@lem4347166 A s' s) (@lem4344174 A B s' s t' t h1)). Qed.
Lemma lem4347269 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4347270 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4347269 B t t' x)). Qed.
Lemma lem4347271 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347273 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4347271 B) (@lem4347270 B t t')). Qed.
Lemma lem4347274 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (EQ_MP (@lem4347273 B t t') (@lem4344255 A B s s' t t' h1)). Qed.
Lemma lem4347337 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4347338 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4347337 B t t' x)). Qed.
Lemma lem4347339 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347341 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4347339 B) (@lem4347338 B t t')). Qed.
Lemma lem4347342 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term172 B t t'.
Proof. exact (EQ_MP (@lem4347341 B t t') (@lem4344255 A B s s' t t' h1)). Qed.
Lemma lem4347379 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4347380 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4347379 B t' t x)). Qed.
Lemma lem4347381 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347383 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4347381 B) (@lem4347380 B t' t)). Qed.
Lemma lem4347384 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 B t' t.
Proof. exact (EQ_MP (@lem4347383 B t' t) (@lem4344173 A B s' s t' t h1)). Qed.
Lemma lem4347447 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4347448 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4347447 B t' t x)). Qed.
Lemma lem4347449 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347451 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4347449 B) (@lem4347448 B t' t)). Qed.
Lemma lem4347452 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term172 B t' t.
Proof. exact (EQ_MP (@lem4347451 B t' t) (@lem4344173 A B s' s t' t h1)). Qed.
Lemma lem4347503 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4347504 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4347503 A s x)). Qed.
Lemma lem4347505 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347507 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4347505 A) (@lem4347504 A s)). Qed.
Lemma lem4347508 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4347507 A s) (@lem4344303 A s h1)). Qed.
Lemma lem4347533 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4347534 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4347533 A s x)). Qed.
Lemma lem4347535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347537 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4347535 A) (@lem4347534 A s)). Qed.
Lemma lem4347538 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4347537 A s) (@lem4344303 A s h1)). Qed.
Lemma lem4347556 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4347557 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4347556 A s' x)). Qed.
Lemma lem4347558 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347560 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4347558 A) (@lem4347557 A s')). Qed.
Lemma lem4347561 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4347560 A s') (@lem4344301 A s' h1)). Qed.
Lemma lem4347586 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4347587 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4347586 A s' x)). Qed.
Lemma lem4347588 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347590 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4347588 A) (@lem4347587 A s')). Qed.
Lemma lem4347591 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4347590 A s') (@lem4344301 A s' h1)). Qed.
Lemma lem4347623 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4347624 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4347623 B t x)). Qed.
Lemma lem4347625 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347627 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4347625 B) (@lem4347624 B t)). Qed.
Lemma lem4347628 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4347627 B t) (@lem4344304 B t h1)). Qed.
Lemma lem4347653 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4347654 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4347653 B t x)). Qed.
Lemma lem4347655 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347657 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4347655 B) (@lem4347654 B t)). Qed.
Lemma lem4347658 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4347657 B t) (@lem4344304 B t h1)). Qed.
Lemma lem4347676 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4347677 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4347676 A s' x)). Qed.
Lemma lem4347678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347680 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4347678 A) (@lem4347677 A s')). Qed.
Lemma lem4347681 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4347680 A s') (@lem4344301 A s' h1)). Qed.
Lemma lem4347706 {A : Type'} (s' : A -> Prop) (x : A) : (term99 A s' x) = (term99 A s' x).
Proof. exact (eq_refl (term99 A s' x)). Qed.
Lemma lem4347707 {A : Type'} (s' : A -> Prop) : (term101 A s') = (term101 A s').
Proof. exact (fun_ext (fun x : A => @lem4347706 A s' x)). Qed.
Lemma lem4347708 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347710 {A : Type'} (s' : A -> Prop) : (term102 A s') = (term102 A s').
Proof. exact (MK_COMB (@lem4347708 A) (@lem4347707 A s')). Qed.
Lemma lem4347711 {A : Type'} (s' : A -> Prop) (h1 : term102 A s') : term102 A s'.
Proof. exact (EQ_MP (@lem4347710 A s') (@lem4344301 A s' h1)). Qed.
Lemma lem4347743 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4347744 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4347743 A s x)). Qed.
Lemma lem4347745 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347747 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4347745 A) (@lem4347744 A s)). Qed.
Lemma lem4347748 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4347747 A s) (@lem4344349 A s h1)). Qed.
Lemma lem4347773 {A : Type'} (s : A -> Prop) (x : A) : (term99 A s x) = (term99 A s x).
Proof. exact (eq_refl (term99 A s x)). Qed.
Lemma lem4347774 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (fun_ext (fun x : A => @lem4347773 A s x)). Qed.
Lemma lem4347775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4347777 {A : Type'} (s : A -> Prop) : (term102 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem4347775 A) (@lem4347774 A s)). Qed.
Lemma lem4347778 {A : Type'} (s : A -> Prop) (h1 : term102 A s) : term102 A s.
Proof. exact (EQ_MP (@lem4347777 A s) (@lem4344349 A s h1)). Qed.
Lemma lem4347796 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4347797 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4347796 B t' x)). Qed.
Lemma lem4347798 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347800 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4347798 B) (@lem4347797 B t')). Qed.
Lemma lem4347801 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4347800 B t') (@lem4344302 B t' h1)). Qed.
Lemma lem4347826 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4347827 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4347826 B t' x)). Qed.
Lemma lem4347828 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347830 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4347828 B) (@lem4347827 B t')). Qed.
Lemma lem4347831 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4347830 B t') (@lem4344302 B t' h1)). Qed.
Lemma lem4347863 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4347864 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4347863 B t x)). Qed.
Lemma lem4347865 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347867 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4347865 B) (@lem4347864 B t)). Qed.
Lemma lem4347868 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4347867 B t) (@lem4344350 B t h1)). Qed.
Lemma lem4347893 {B : Type'} (t : B -> Prop) (x : B) : (term99 B t x) = (term99 B t x).
Proof. exact (eq_refl (term99 B t x)). Qed.
Lemma lem4347894 {B : Type'} (t : B -> Prop) : (term101 B t) = (term101 B t).
Proof. exact (fun_ext (fun x : B => @lem4347893 B t x)). Qed.
Lemma lem4347895 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347897 {B : Type'} (t : B -> Prop) : (term102 B t) = (term102 B t).
Proof. exact (MK_COMB (@lem4347895 B) (@lem4347894 B t)). Qed.
Lemma lem4347898 {B : Type'} (t : B -> Prop) (h1 : term102 B t) : term102 B t.
Proof. exact (EQ_MP (@lem4347897 B t) (@lem4344350 B t h1)). Qed.
Lemma lem4347916 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4347917 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4347916 B t' x)). Qed.
Lemma lem4347918 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347920 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4347918 B) (@lem4347917 B t')). Qed.
Lemma lem4347921 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4347920 B t') (@lem4344302 B t' h1)). Qed.
Lemma lem4347946 {B : Type'} (t' : B -> Prop) (x : B) : (term99 B t' x) = (term99 B t' x).
Proof. exact (eq_refl (term99 B t' x)). Qed.
Lemma lem4347947 {B : Type'} (t' : B -> Prop) : (term101 B t') = (term101 B t').
Proof. exact (fun_ext (fun x : B => @lem4347946 B t' x)). Qed.
Lemma lem4347948 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4347950 {B : Type'} (t' : B -> Prop) : (term102 B t') = (term102 B t').
Proof. exact (MK_COMB (@lem4347948 B) (@lem4347947 B t')). Qed.
Lemma lem4347951 {B : Type'} (t' : B -> Prop) (h1 : term102 B t') : term102 B t'.
Proof. exact (EQ_MP (@lem4347950 B t') (@lem4344302 B t' h1)). Qed.
Lemma lem4348008 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term163 A s s' x) = (term163 A s s' x).
Proof. exact (eq_refl (term163 A s s' x)). Qed.
Lemma lem4348009 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term171 A s s') = (term171 A s s').
Proof. exact (fun_ext (fun x : A => @lem4348008 A s s' x)). Qed.
Lemma lem4348010 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4348012 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (MK_COMB (@lem4348010 A) (@lem4348009 A s s')). Qed.
Lemma lem4348013 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 A s s'.
Proof. exact (EQ_MP (@lem4348012 A s s') (@lem4344400 A B s' s t' t h1)). Qed.
Lemma lem4348050 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x : B) : (term163 B t t' x) = (term163 B t t' x).
Proof. exact (eq_refl (term163 B t t' x)). Qed.
Lemma lem4348051 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term171 B t t') = (term171 B t t').
Proof. exact (fun_ext (fun x : B => @lem4348050 B t t' x)). Qed.
Lemma lem4348052 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4348054 {B : Type'} (t : B -> Prop) (t' : B -> Prop) : (term172 B t t') = (term172 B t t').
Proof. exact (MK_COMB (@lem4348052 B) (@lem4348051 B t t')). Qed.
Lemma lem4348055 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 B t t'.
Proof. exact (EQ_MP (@lem4348054 B t t') (@lem4344398 A B s' s t' t h1)). Qed.
Lemma lem4348157 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term163 A s' s x) = (term163 A s' s x).
Proof. exact (eq_refl (term163 A s' s x)). Qed.
Lemma lem4348158 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term171 A s' s) = (term171 A s' s).
Proof. exact (fun_ext (fun x : A => @lem4348157 A s' s x)). Qed.
Lemma lem4348159 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4348161 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term172 A s' s) = (term172 A s' s).
Proof. exact (MK_COMB (@lem4348159 A) (@lem4348158 A s' s)). Qed.
Lemma lem4348162 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 A s' s.
Proof. exact (EQ_MP (@lem4348161 A s' s) (@lem4344399 A B s' s t' t h1)). Qed.
Lemma lem4348199 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x : B) : (term163 B t' t x) = (term163 B t' t x).
Proof. exact (eq_refl (term163 B t' t x)). Qed.
Lemma lem4348200 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term171 B t' t) = (term171 B t' t).
Proof. exact (fun_ext (fun x : B => @lem4348199 B t' t x)). Qed.
Lemma lem4348201 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4348203 {B : Type'} (t' : B -> Prop) (t : B -> Prop) : (term172 B t' t) = (term172 B t' t).
Proof. exact (MK_COMB (@lem4348201 B) (@lem4348200 B t' t)). Qed.
Lemma lem4348204 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term172 B t' t.
Proof. exact (EQ_MP (@lem4348203 B t' t) (@lem4344397 A B s' s t' t h1)). Qed.
Lemma lem4348250 {A : Type'} (_49551 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49551.
Proof. exact (@lem4344436 A s h1 _49551). Qed.
Lemma lem4348251 {A : Type'} (s : A -> Prop) (_49551 : A) : (term156 A s _49551) = (term99 A s _49551).
Proof. exact (eq_refl (term156 A s _49551)). Qed.
Lemma lem4348256 {A : Type'} (_49553 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49553.
Proof. exact (@lem4344466 A s h1 _49553). Qed.
Lemma lem4348257 {A : Type'} (s : A -> Prop) (_49553 : A) : (term156 A s _49553) = (term99 A s _49553).
Proof. exact (eq_refl (term156 A s _49553)). Qed.
Lemma lem4348262 {A : Type'} (_49555 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49555.
Proof. exact (@lem4344496 A s h1 _49555). Qed.
Lemma lem4348263 {A : Type'} (s : A -> Prop) (_49555 : A) : (term156 A s _49555) = (term99 A s _49555).
Proof. exact (eq_refl (term156 A s _49555)). Qed.
Lemma lem4348265 {A : Type'} (_49556 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49556.
Proof. exact (@lem4344519 A s' h1 _49556). Qed.
Lemma lem4348266 {A : Type'} (s' : A -> Prop) (_49556 : A) : (term156 A s' _49556) = (term99 A s' _49556).
Proof. exact (eq_refl (term156 A s' _49556)). Qed.
Lemma lem4348274 {A : Type'} (_49559 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49559.
Proof. exact (@lem4344556 A s h1 _49559). Qed.
Lemma lem4348275 {A : Type'} (s : A -> Prop) (_49559 : A) : (term156 A s _49559) = (term99 A s _49559).
Proof. exact (eq_refl (term156 A s _49559)). Qed.
Lemma lem4348277 {A : Type'} (_49560 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49560.
Proof. exact (@lem4344579 A s' h1 _49560). Qed.
Lemma lem4348278 {A : Type'} (s' : A -> Prop) (_49560 : A) : (term156 A s' _49560) = (term99 A s' _49560).
Proof. exact (eq_refl (term156 A s' _49560)). Qed.
Lemma lem4348286 {A : Type'} (_49563 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49563.
Proof. exact (@lem4344616 A s h1 _49563). Qed.
Lemma lem4348287 {A : Type'} (s : A -> Prop) (_49563 : A) : (term156 A s _49563) = (term99 A s _49563).
Proof. exact (eq_refl (term156 A s _49563)). Qed.
Lemma lem4348289 {A : Type'} (_49564 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49564.
Proof. exact (@lem4344639 A s' h1 _49564). Qed.
Lemma lem4348290 {A : Type'} (s' : A -> Prop) (_49564 : A) : (term156 A s' _49564) = (term99 A s' _49564).
Proof. exact (eq_refl (term156 A s' _49564)). Qed.
Lemma lem4348298 {B : Type'} (_49567 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49567.
Proof. exact (@lem4344676 B t h1 _49567). Qed.
Lemma lem4348299 {B : Type'} (t : B -> Prop) (_49567 : B) : (term156 B t _49567) = (term99 B t _49567).
Proof. exact (eq_refl (term156 B t _49567)). Qed.
Lemma lem4348301 {A : Type'} (_49568 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49568.
Proof. exact (@lem4344699 A s' h1 _49568). Qed.
Lemma lem4348302 {A : Type'} (s' : A -> Prop) (_49568 : A) : (term156 A s' _49568) = (term99 A s' _49568).
Proof. exact (eq_refl (term156 A s' _49568)). Qed.
Lemma lem4348310 {B : Type'} (_49571 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49571.
Proof. exact (@lem4344736 B t h1 _49571). Qed.
Lemma lem4348311 {B : Type'} (t : B -> Prop) (_49571 : B) : (term156 B t _49571) = (term99 B t _49571).
Proof. exact (eq_refl (term156 B t _49571)). Qed.
Lemma lem4348313 {A : Type'} (_49572 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49572.
Proof. exact (@lem4344759 A s' h1 _49572). Qed.
Lemma lem4348314 {A : Type'} (s' : A -> Prop) (_49572 : A) : (term156 A s' _49572) = (term99 A s' _49572).
Proof. exact (eq_refl (term156 A s' _49572)). Qed.
Lemma lem4348322 {B : Type'} (_49575 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49575.
Proof. exact (@lem4344796 B t h1 _49575). Qed.
Lemma lem4348323 {B : Type'} (t : B -> Prop) (_49575 : B) : (term156 B t _49575) = (term99 B t _49575).
Proof. exact (eq_refl (term156 B t _49575)). Qed.
Lemma lem4348328 {B : Type'} (_49577 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49577.
Proof. exact (@lem4344826 B t h1 _49577). Qed.
Lemma lem4348329 {B : Type'} (t : B -> Prop) (_49577 : B) : (term156 B t _49577) = (term99 B t _49577).
Proof. exact (eq_refl (term156 B t _49577)). Qed.
Lemma lem4348334 {B : Type'} (_49579 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49579.
Proof. exact (@lem4344856 B t h1 _49579). Qed.
Lemma lem4348335 {B : Type'} (t : B -> Prop) (_49579 : B) : (term156 B t _49579) = (term99 B t _49579).
Proof. exact (eq_refl (term156 B t _49579)). Qed.
Lemma lem4348337 {A : Type'} (_49580 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49580.
Proof. exact (@lem4344879 A s' h1 _49580). Qed.
Lemma lem4348338 {A : Type'} (s' : A -> Prop) (_49580 : A) : (term156 A s' _49580) = (term99 A s' _49580).
Proof. exact (eq_refl (term156 A s' _49580)). Qed.
Lemma lem4348346 {A B : Type'} (_49583 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 A s s' _49583.
Proof. exact (@lem4344922 A B s s' t t' h1 _49583). Qed.
Lemma lem4348347 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49583 : A) : (term761 A s s' _49583) = (term163 A s s' _49583).
Proof. exact (eq_refl (term761 A s s' _49583)). Qed.
Lemma lem4348352 {A : Type'} (_49585 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49585.
Proof. exact (@lem4344958 A s' h1 _49585). Qed.
Lemma lem4348353 {A : Type'} (s' : A -> Prop) (_49585 : A) : (term156 A s' _49585) = (term99 A s' _49585).
Proof. exact (eq_refl (term156 A s' _49585)). Qed.
Lemma lem4348361 {A : Type'} (_49588 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49588.
Proof. exact (@lem4345007 A s' h1 _49588). Qed.
Lemma lem4348362 {A : Type'} (s' : A -> Prop) (_49588 : A) : (term156 A s' _49588) = (term99 A s' _49588).
Proof. exact (eq_refl (term156 A s' _49588)). Qed.
Lemma lem4348370 {A : Type'} (_49591 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49591.
Proof. exact (@lem4345056 A s' h1 _49591). Qed.
Lemma lem4348371 {A : Type'} (s' : A -> Prop) (_49591 : A) : (term156 A s' _49591) = (term99 A s' _49591).
Proof. exact (eq_refl (term156 A s' _49591)). Qed.
Lemma lem4348385 {A B : Type'} (_49596 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 B t t' _49596.
Proof. exact (@lem4345131 A B s s' t t' h1 _49596). Qed.
Lemma lem4348386 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49596 : B) : (term761 B t t' _49596) = (term163 B t t' _49596).
Proof. exact (eq_refl (term761 B t t' _49596)). Qed.
Lemma lem4348388 {A : Type'} (_49597 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49597.
Proof. exact (@lem4345154 A s' h1 _49597). Qed.
Lemma lem4348389 {A : Type'} (s' : A -> Prop) (_49597 : A) : (term156 A s' _49597) = (term99 A s' _49597).
Proof. exact (eq_refl (term156 A s' _49597)). Qed.
Lemma lem4348397 {A : Type'} (_49600 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49600.
Proof. exact (@lem4345203 A s' h1 _49600). Qed.
Lemma lem4348398 {A : Type'} (s' : A -> Prop) (_49600 : A) : (term156 A s' _49600) = (term99 A s' _49600).
Proof. exact (eq_refl (term156 A s' _49600)). Qed.
Lemma lem4348400 {A B : Type'} (_49601 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 A s s' _49601.
Proof. exact (@lem4345216 A B s s' t t' h1 _49601). Qed.
Lemma lem4348401 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49601 : A) : (term761 A s s' _49601) = (term163 A s s' _49601).
Proof. exact (eq_refl (term761 A s s' _49601)). Qed.
Lemma lem4348406 {A : Type'} (_49603 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49603.
Proof. exact (@lem4345252 A s' h1 _49603). Qed.
Lemma lem4348407 {A : Type'} (s' : A -> Prop) (_49603 : A) : (term156 A s' _49603) = (term99 A s' _49603).
Proof. exact (eq_refl (term156 A s' _49603)). Qed.
Lemma lem4348418 {A : Type'} (_49607 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49607.
Proof. exact (@lem4345308 A s h1 _49607). Qed.
Lemma lem4348419 {A : Type'} (s : A -> Prop) (_49607 : A) : (term156 A s _49607) = (term99 A s _49607).
Proof. exact (eq_refl (term156 A s _49607)). Qed.
Lemma lem4348424 {A : Type'} (_49609 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49609.
Proof. exact (@lem4345338 A s h1 _49609). Qed.
Lemma lem4348425 {A : Type'} (s : A -> Prop) (_49609 : A) : (term156 A s _49609) = (term99 A s _49609).
Proof. exact (eq_refl (term156 A s _49609)). Qed.
Lemma lem4348430 {A : Type'} (_49611 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49611.
Proof. exact (@lem4345368 A s h1 _49611). Qed.
Lemma lem4348431 {A : Type'} (s : A -> Prop) (_49611 : A) : (term156 A s _49611) = (term99 A s _49611).
Proof. exact (eq_refl (term156 A s _49611)). Qed.
Lemma lem4348433 {B : Type'} (_49612 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49612.
Proof. exact (@lem4345391 B t' h1 _49612). Qed.
Lemma lem4348434 {B : Type'} (t' : B -> Prop) (_49612 : B) : (term156 B t' _49612) = (term99 B t' _49612).
Proof. exact (eq_refl (term156 B t' _49612)). Qed.
Lemma lem4348442 {A : Type'} (_49615 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49615.
Proof. exact (@lem4345428 A s h1 _49615). Qed.
Lemma lem4348443 {A : Type'} (s : A -> Prop) (_49615 : A) : (term156 A s _49615) = (term99 A s _49615).
Proof. exact (eq_refl (term156 A s _49615)). Qed.
Lemma lem4348445 {B : Type'} (_49616 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49616.
Proof. exact (@lem4345451 B t' h1 _49616). Qed.
Lemma lem4348446 {B : Type'} (t' : B -> Prop) (_49616 : B) : (term156 B t' _49616) = (term99 B t' _49616).
Proof. exact (eq_refl (term156 B t' _49616)). Qed.
Lemma lem4348454 {A : Type'} (_49619 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49619.
Proof. exact (@lem4345488 A s h1 _49619). Qed.
Lemma lem4348455 {A : Type'} (s : A -> Prop) (_49619 : A) : (term156 A s _49619) = (term99 A s _49619).
Proof. exact (eq_refl (term156 A s _49619)). Qed.
Lemma lem4348457 {B : Type'} (_49620 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49620.
Proof. exact (@lem4345511 B t' h1 _49620). Qed.
Lemma lem4348458 {B : Type'} (t' : B -> Prop) (_49620 : B) : (term156 B t' _49620) = (term99 B t' _49620).
Proof. exact (eq_refl (term156 B t' _49620)). Qed.
Lemma lem4348466 {B : Type'} (_49623 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49623.
Proof. exact (@lem4345548 B t h1 _49623). Qed.
Lemma lem4348467 {B : Type'} (t : B -> Prop) (_49623 : B) : (term156 B t _49623) = (term99 B t _49623).
Proof. exact (eq_refl (term156 B t _49623)). Qed.
Lemma lem4348469 {B : Type'} (_49624 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49624.
Proof. exact (@lem4345571 B t' h1 _49624). Qed.
Lemma lem4348470 {B : Type'} (t' : B -> Prop) (_49624 : B) : (term156 B t' _49624) = (term99 B t' _49624).
Proof. exact (eq_refl (term156 B t' _49624)). Qed.
Lemma lem4348478 {B : Type'} (_49627 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49627.
Proof. exact (@lem4345608 B t h1 _49627). Qed.
Lemma lem4348479 {B : Type'} (t : B -> Prop) (_49627 : B) : (term156 B t _49627) = (term99 B t _49627).
Proof. exact (eq_refl (term156 B t _49627)). Qed.
Lemma lem4348481 {B : Type'} (_49628 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49628.
Proof. exact (@lem4345631 B t' h1 _49628). Qed.
Lemma lem4348482 {B : Type'} (t' : B -> Prop) (_49628 : B) : (term156 B t' _49628) = (term99 B t' _49628).
Proof. exact (eq_refl (term156 B t' _49628)). Qed.
Lemma lem4348490 {B : Type'} (_49631 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49631.
Proof. exact (@lem4345668 B t h1 _49631). Qed.
Lemma lem4348491 {B : Type'} (t : B -> Prop) (_49631 : B) : (term156 B t _49631) = (term99 B t _49631).
Proof. exact (eq_refl (term156 B t _49631)). Qed.
Lemma lem4348496 {B : Type'} (_49633 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49633.
Proof. exact (@lem4345698 B t h1 _49633). Qed.
Lemma lem4348497 {B : Type'} (t : B -> Prop) (_49633 : B) : (term156 B t _49633) = (term99 B t _49633).
Proof. exact (eq_refl (term156 B t _49633)). Qed.
Lemma lem4348502 {B : Type'} (_49635 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49635.
Proof. exact (@lem4345728 B t h1 _49635). Qed.
Lemma lem4348503 {B : Type'} (t : B -> Prop) (_49635 : B) : (term156 B t _49635) = (term99 B t _49635).
Proof. exact (eq_refl (term156 B t _49635)). Qed.
Lemma lem4348505 {B : Type'} (_49636 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49636.
Proof. exact (@lem4345751 B t' h1 _49636). Qed.
Lemma lem4348506 {B : Type'} (t' : B -> Prop) (_49636 : B) : (term156 B t' _49636) = (term99 B t' _49636).
Proof. exact (eq_refl (term156 B t' _49636)). Qed.
Lemma lem4348514 {A B : Type'} (_49639 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 A s s' _49639.
Proof. exact (@lem4345794 A B s s' t t' h1 _49639). Qed.
Lemma lem4348515 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49639 : A) : (term761 A s s' _49639) = (term163 A s s' _49639).
Proof. exact (eq_refl (term761 A s s' _49639)). Qed.
Lemma lem4348520 {B : Type'} (_49641 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49641.
Proof. exact (@lem4345830 B t' h1 _49641). Qed.
Lemma lem4348521 {B : Type'} (t' : B -> Prop) (_49641 : B) : (term156 B t' _49641) = (term99 B t' _49641).
Proof. exact (eq_refl (term156 B t' _49641)). Qed.
Lemma lem4348529 {B : Type'} (_49644 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49644.
Proof. exact (@lem4345879 B t' h1 _49644). Qed.
Lemma lem4348530 {B : Type'} (t' : B -> Prop) (_49644 : B) : (term156 B t' _49644) = (term99 B t' _49644).
Proof. exact (eq_refl (term156 B t' _49644)). Qed.
Lemma lem4348535 {A B : Type'} (_49646 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 B t t' _49646.
Proof. exact (@lem4345905 A B s s' t t' h1 _49646). Qed.
Lemma lem4348536 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49646 : B) : (term761 B t t' _49646) = (term163 B t t' _49646).
Proof. exact (eq_refl (term761 B t t' _49646)). Qed.
Lemma lem4348538 {B : Type'} (_49647 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49647.
Proof. exact (@lem4345928 B t' h1 _49647). Qed.
Lemma lem4348539 {B : Type'} (t' : B -> Prop) (_49647 : B) : (term156 B t' _49647) = (term99 B t' _49647).
Proof. exact (eq_refl (term156 B t' _49647)). Qed.
Lemma lem4348553 {A B : Type'} (_49652 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 B t t' _49652.
Proof. exact (@lem4346003 A B s s' t t' h1 _49652). Qed.
Lemma lem4348554 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49652 : B) : (term761 B t t' _49652) = (term163 B t t' _49652).
Proof. exact (eq_refl (term761 B t t' _49652)). Qed.
Lemma lem4348556 {B : Type'} (_49653 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49653.
Proof. exact (@lem4346026 B t' h1 _49653). Qed.
Lemma lem4348557 {B : Type'} (t' : B -> Prop) (_49653 : B) : (term156 B t' _49653) = (term99 B t' _49653).
Proof. exact (eq_refl (term156 B t' _49653)). Qed.
Lemma lem4348565 {B : Type'} (_49656 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49656.
Proof. exact (@lem4346075 B t' h1 _49656). Qed.
Lemma lem4348566 {B : Type'} (t' : B -> Prop) (_49656 : B) : (term156 B t' _49656) = (term99 B t' _49656).
Proof. exact (eq_refl (term156 B t' _49656)). Qed.
Lemma lem4348574 {B : Type'} (_49659 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49659.
Proof. exact (@lem4346124 B t' h1 _49659). Qed.
Lemma lem4348575 {B : Type'} (t' : B -> Prop) (_49659 : B) : (term156 B t' _49659) = (term99 B t' _49659).
Proof. exact (eq_refl (term156 B t' _49659)). Qed.
Lemma lem4348589 {A : Type'} (_49664 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49664.
Proof. exact (@lem4346199 A s h1 _49664). Qed.
Lemma lem4348590 {A : Type'} (s : A -> Prop) (_49664 : A) : (term156 A s _49664) = (term99 A s _49664).
Proof. exact (eq_refl (term156 A s _49664)). Qed.
Lemma lem4348598 {A : Type'} (_49667 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49667.
Proof. exact (@lem4346248 A s h1 _49667). Qed.
Lemma lem4348599 {A : Type'} (s : A -> Prop) (_49667 : A) : (term156 A s _49667) = (term99 A s _49667).
Proof. exact (eq_refl (term156 A s _49667)). Qed.
Lemma lem4348607 {A : Type'} (_49670 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49670.
Proof. exact (@lem4346297 A s h1 _49670). Qed.
Lemma lem4348608 {A : Type'} (s : A -> Prop) (_49670 : A) : (term156 A s _49670) = (term99 A s _49670).
Proof. exact (eq_refl (term156 A s _49670)). Qed.
Lemma lem4348610 {A B : Type'} (_49671 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 A s' s _49671.
Proof. exact (@lem4346326 A B s' s t' t h1 _49671). Qed.
Lemma lem4348611 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49671 : A) : (term761 A s' s _49671) = (term163 A s' s _49671).
Proof. exact (eq_refl (term761 A s' s _49671)). Qed.
Lemma lem4348625 {A : Type'} (_49676 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49676.
Proof. exact (@lem4346395 A s h1 _49676). Qed.
Lemma lem4348626 {A : Type'} (s : A -> Prop) (_49676 : A) : (term156 A s _49676) = (term99 A s _49676).
Proof. exact (eq_refl (term156 A s _49676)). Qed.
Lemma lem4348628 {A B : Type'} (_49677 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 A s' s _49677.
Proof. exact (@lem4346424 A B s' s t' t h1 _49677). Qed.
Lemma lem4348629 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49677 : A) : (term761 A s' s _49677) = (term163 A s' s _49677).
Proof. exact (eq_refl (term761 A s' s _49677)). Qed.
Lemma lem4348634 {A : Type'} (_49679 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49679.
Proof. exact (@lem4346444 A s h1 _49679). Qed.
Lemma lem4348635 {A : Type'} (s : A -> Prop) (_49679 : A) : (term156 A s _49679) = (term99 A s _49679).
Proof. exact (eq_refl (term156 A s _49679)). Qed.
Lemma lem4348643 {A : Type'} (_49682 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49682.
Proof. exact (@lem4346493 A s h1 _49682). Qed.
Lemma lem4348644 {A : Type'} (s : A -> Prop) (_49682 : A) : (term156 A s _49682) = (term99 A s _49682).
Proof. exact (eq_refl (term156 A s _49682)). Qed.
Lemma lem4348649 {A B : Type'} (_49684 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 B t' t _49684.
Proof. exact (@lem4346535 A B s' s t' t h1 _49684). Qed.
Lemma lem4348650 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49684 : B) : (term761 B t' t _49684) = (term163 B t' t _49684).
Proof. exact (eq_refl (term761 B t' t _49684)). Qed.
Lemma lem4348661 {B : Type'} (_49688 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49688.
Proof. exact (@lem4346591 B t h1 _49688). Qed.
Lemma lem4348662 {B : Type'} (t : B -> Prop) (_49688 : B) : (term156 B t _49688) = (term99 B t _49688).
Proof. exact (eq_refl (term156 B t _49688)). Qed.
Lemma lem4348667 {A B : Type'} (_49690 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 B t' t _49690.
Proof. exact (@lem4346633 A B s' s t' t h1 _49690). Qed.
Lemma lem4348668 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49690 : B) : (term761 B t' t _49690) = (term163 B t' t _49690).
Proof. exact (eq_refl (term761 B t' t _49690)). Qed.
Lemma lem4348670 {B : Type'} (_49691 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49691.
Proof. exact (@lem4346640 B t h1 _49691). Qed.
Lemma lem4348671 {B : Type'} (t : B -> Prop) (_49691 : B) : (term156 B t _49691) = (term99 B t _49691).
Proof. exact (eq_refl (term156 B t _49691)). Qed.
Lemma lem4348679 {B : Type'} (_49694 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49694.
Proof. exact (@lem4346689 B t h1 _49694). Qed.
Lemma lem4348680 {B : Type'} (t : B -> Prop) (_49694 : B) : (term156 B t _49694) = (term99 B t _49694).
Proof. exact (eq_refl (term156 B t _49694)). Qed.
Lemma lem4348682 {A B : Type'} (_49695 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 A s' s _49695.
Proof. exact (@lem4346718 A B s' s t' t h1 _49695). Qed.
Lemma lem4348683 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49695 : A) : (term761 A s' s _49695) = (term163 A s' s _49695).
Proof. exact (eq_refl (term761 A s' s _49695)). Qed.
Lemma lem4348697 {B : Type'} (_49700 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49700.
Proof. exact (@lem4346787 B t h1 _49700). Qed.
Lemma lem4348698 {B : Type'} (t : B -> Prop) (_49700 : B) : (term156 B t _49700) = (term99 B t _49700).
Proof. exact (eq_refl (term156 B t _49700)). Qed.
Lemma lem4348706 {B : Type'} (_49703 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49703.
Proof. exact (@lem4346836 B t h1 _49703). Qed.
Lemma lem4348707 {B : Type'} (t : B -> Prop) (_49703 : B) : (term156 B t _49703) = (term99 B t _49703).
Proof. exact (eq_refl (term156 B t _49703)). Qed.
Lemma lem4348715 {B : Type'} (_49706 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49706.
Proof. exact (@lem4346885 B t h1 _49706). Qed.
Lemma lem4348716 {B : Type'} (t : B -> Prop) (_49706 : B) : (term156 B t _49706) = (term99 B t _49706).
Proof. exact (eq_refl (term156 B t _49706)). Qed.
Lemma lem4348721 {A B : Type'} (_49708 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 B t' t _49708.
Proof. exact (@lem4346927 A B s' s t' t h1 _49708). Qed.
Lemma lem4348722 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49708 : B) : (term761 B t' t _49708) = (term163 B t' t _49708).
Proof. exact (eq_refl (term761 B t' t _49708)). Qed.
Lemma lem4348733 {A B : Type'} (_49712 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 A s s' _49712.
Proof. exact (@lem4346989 A B s s' t t' h1 _49712). Qed.
Lemma lem4348734 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49712 : A) : (term761 A s s' _49712) = (term163 A s s' _49712).
Proof. exact (eq_refl (term761 A s s' _49712)). Qed.
Lemma lem4348745 {A B : Type'} (_49716 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 A s s' _49716.
Proof. exact (@lem4347057 A B s s' t t' h1 _49716). Qed.
Lemma lem4348746 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49716 : A) : (term761 A s s' _49716) = (term163 A s s' _49716).
Proof. exact (eq_refl (term761 A s s' _49716)). Qed.
Lemma lem4348751 {A B : Type'} (_49718 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 A s' s _49718.
Proof. exact (@lem4347099 A B s' s t' t h1 _49718). Qed.
Lemma lem4348752 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49718 : A) : (term761 A s' s _49718) = (term163 A s' s _49718).
Proof. exact (eq_refl (term761 A s' s _49718)). Qed.
Lemma lem4348763 {A B : Type'} (_49722 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 A s' s _49722.
Proof. exact (@lem4347167 A B s' s t' t h1 _49722). Qed.
Lemma lem4348764 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49722 : A) : (term761 A s' s _49722) = (term163 A s' s _49722).
Proof. exact (eq_refl (term761 A s' s _49722)). Qed.
Lemma lem4348784 {A B : Type'} (_49729 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 B t t' _49729.
Proof. exact (@lem4347274 A B s s' t t' h1 _49729). Qed.
Lemma lem4348785 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49729 : B) : (term761 B t t' _49729) = (term163 B t t' _49729).
Proof. exact (eq_refl (term761 B t t' _49729)). Qed.
Lemma lem4348796 {A B : Type'} (_49733 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term761 B t t' _49733.
Proof. exact (@lem4347342 A B s s' t t' h1 _49733). Qed.
Lemma lem4348797 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49733 : B) : (term761 B t t' _49733) = (term163 B t t' _49733).
Proof. exact (eq_refl (term761 B t t' _49733)). Qed.
Lemma lem4348802 {A B : Type'} (_49735 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 B t' t _49735.
Proof. exact (@lem4347384 A B s' s t' t h1 _49735). Qed.
Lemma lem4348803 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49735 : B) : (term761 B t' t _49735) = (term163 B t' t _49735).
Proof. exact (eq_refl (term761 B t' t _49735)). Qed.
Lemma lem4348814 {A B : Type'} (_49739 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term761 B t' t _49739.
Proof. exact (@lem4347452 A B s' s t' t h1 _49739). Qed.
Lemma lem4348815 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49739 : B) : (term761 B t' t _49739) = (term163 B t' t _49739).
Proof. exact (eq_refl (term761 B t' t _49739)). Qed.
Lemma lem4348826 {A : Type'} (_49743 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49743.
Proof. exact (@lem4347508 A s h1 _49743). Qed.
Lemma lem4348827 {A : Type'} (s : A -> Prop) (_49743 : A) : (term156 A s _49743) = (term99 A s _49743).
Proof. exact (eq_refl (term156 A s _49743)). Qed.
Lemma lem4348832 {A : Type'} (_49745 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49745.
Proof. exact (@lem4347538 A s h1 _49745). Qed.
Lemma lem4348833 {A : Type'} (s : A -> Prop) (_49745 : A) : (term156 A s _49745) = (term99 A s _49745).
Proof. exact (eq_refl (term156 A s _49745)). Qed.
Lemma lem4348835 {A : Type'} (_49746 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49746.
Proof. exact (@lem4347561 A s' h1 _49746). Qed.
Lemma lem4348836 {A : Type'} (s' : A -> Prop) (_49746 : A) : (term156 A s' _49746) = (term99 A s' _49746).
Proof. exact (eq_refl (term156 A s' _49746)). Qed.
Lemma lem4348841 {A : Type'} (_49748 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49748.
Proof. exact (@lem4347591 A s' h1 _49748). Qed.
Lemma lem4348842 {A : Type'} (s' : A -> Prop) (_49748 : A) : (term156 A s' _49748) = (term99 A s' _49748).
Proof. exact (eq_refl (term156 A s' _49748)). Qed.
Lemma lem4348850 {B : Type'} (_49751 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49751.
Proof. exact (@lem4347628 B t h1 _49751). Qed.
Lemma lem4348851 {B : Type'} (t : B -> Prop) (_49751 : B) : (term156 B t _49751) = (term99 B t _49751).
Proof. exact (eq_refl (term156 B t _49751)). Qed.
Lemma lem4348856 {B : Type'} (_49753 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49753.
Proof. exact (@lem4347658 B t h1 _49753). Qed.
Lemma lem4348857 {B : Type'} (t : B -> Prop) (_49753 : B) : (term156 B t _49753) = (term99 B t _49753).
Proof. exact (eq_refl (term156 B t _49753)). Qed.
Lemma lem4348859 {A : Type'} (_49754 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49754.
Proof. exact (@lem4347681 A s' h1 _49754). Qed.
Lemma lem4348860 {A : Type'} (s' : A -> Prop) (_49754 : A) : (term156 A s' _49754) = (term99 A s' _49754).
Proof. exact (eq_refl (term156 A s' _49754)). Qed.
Lemma lem4348865 {A : Type'} (_49756 : A) (s' : A -> Prop) (h1 : term102 A s') : term156 A s' _49756.
Proof. exact (@lem4347711 A s' h1 _49756). Qed.
Lemma lem4348866 {A : Type'} (s' : A -> Prop) (_49756 : A) : (term156 A s' _49756) = (term99 A s' _49756).
Proof. exact (eq_refl (term156 A s' _49756)). Qed.
Lemma lem4348874 {A : Type'} (_49759 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49759.
Proof. exact (@lem4347748 A s h1 _49759). Qed.
Lemma lem4348875 {A : Type'} (s : A -> Prop) (_49759 : A) : (term156 A s _49759) = (term99 A s _49759).
Proof. exact (eq_refl (term156 A s _49759)). Qed.
Lemma lem4348880 {A : Type'} (_49761 : A) (s : A -> Prop) (h1 : term102 A s) : term156 A s _49761.
Proof. exact (@lem4347778 A s h1 _49761). Qed.
Lemma lem4348881 {A : Type'} (s : A -> Prop) (_49761 : A) : (term156 A s _49761) = (term99 A s _49761).
Proof. exact (eq_refl (term156 A s _49761)). Qed.
Lemma lem4348883 {B : Type'} (_49762 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49762.
Proof. exact (@lem4347801 B t' h1 _49762). Qed.
Lemma lem4348884 {B : Type'} (t' : B -> Prop) (_49762 : B) : (term156 B t' _49762) = (term99 B t' _49762).
Proof. exact (eq_refl (term156 B t' _49762)). Qed.
Lemma lem4348889 {B : Type'} (_49764 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49764.
Proof. exact (@lem4347831 B t' h1 _49764). Qed.
Lemma lem4348890 {B : Type'} (t' : B -> Prop) (_49764 : B) : (term156 B t' _49764) = (term99 B t' _49764).
Proof. exact (eq_refl (term156 B t' _49764)). Qed.
Lemma lem4348898 {B : Type'} (_49767 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49767.
Proof. exact (@lem4347868 B t h1 _49767). Qed.
Lemma lem4348899 {B : Type'} (t : B -> Prop) (_49767 : B) : (term156 B t _49767) = (term99 B t _49767).
Proof. exact (eq_refl (term156 B t _49767)). Qed.
Lemma lem4348904 {B : Type'} (_49769 : B) (t : B -> Prop) (h1 : term102 B t) : term156 B t _49769.
Proof. exact (@lem4347898 B t h1 _49769). Qed.
Lemma lem4348905 {B : Type'} (t : B -> Prop) (_49769 : B) : (term156 B t _49769) = (term99 B t _49769).
Proof. exact (eq_refl (term156 B t _49769)). Qed.
Lemma lem4348907 {B : Type'} (_49770 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49770.
Proof. exact (@lem4347921 B t' h1 _49770). Qed.
Lemma lem4348908 {B : Type'} (t' : B -> Prop) (_49770 : B) : (term156 B t' _49770) = (term99 B t' _49770).
Proof. exact (eq_refl (term156 B t' _49770)). Qed.
Lemma lem4348913 {B : Type'} (_49772 : B) (t' : B -> Prop) (h1 : term102 B t') : term156 B t' _49772.
Proof. exact (@lem4347951 B t' h1 _49772). Qed.
Lemma lem4348914 {B : Type'} (t' : B -> Prop) (_49772 : B) : (term156 B t' _49772) = (term99 B t' _49772).
Proof. exact (eq_refl (term156 B t' _49772)). Qed.
Lemma lem4348925 {A B : Type'} (_49776 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term761 A s s' _49776.
Proof. exact (@lem4348013 A B s' s t' t h1 _49776). Qed.
Lemma lem4348926 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49776 : A) : (term761 A s s' _49776) = (term163 A s s' _49776).
Proof. exact (eq_refl (term761 A s s' _49776)). Qed.
Lemma lem4348931 {A B : Type'} (_49778 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term761 B t t' _49778.
Proof. exact (@lem4348055 A B s' s t' t h1 _49778). Qed.
Lemma lem4348932 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49778 : B) : (term761 B t t' _49778) = (term163 B t t' _49778).
Proof. exact (eq_refl (term761 B t t' _49778)). Qed.
Lemma lem4348952 {A B : Type'} (_49785 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term761 A s' s _49785.
Proof. exact (@lem4348162 A B s' s t' t h1 _49785). Qed.
Lemma lem4348953 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49785 : A) : (term761 A s' s _49785) = (term163 A s' s _49785).
Proof. exact (eq_refl (term761 A s' s _49785)). Qed.
Lemma lem4348958 {A B : Type'} (_49787 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term761 B t' t _49787.
Proof. exact (@lem4348204 A B s' s t' t h1 _49787). Qed.
Lemma lem4348959 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49787 : B) : (term761 B t' t _49787) = (term163 B t' t _49787).
Proof. exact (eq_refl (term761 B t' t _49787)). Qed.
Lemma lem4348970 {A : Type'} (_49551 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49551.
Proof. exact (EQ_MP (@lem4348251 A s _49551) (@lem4348250 A _49551 s h1)). Qed.
Lemma lem4348982 {A : Type'} (_49553 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49553.
Proof. exact (EQ_MP (@lem4348257 A s _49553) (@lem4348256 A _49553 s h1)). Qed.
Lemma lem4348994 {A : Type'} (_49555 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49555.
Proof. exact (EQ_MP (@lem4348263 A s _49555) (@lem4348262 A _49555 s h1)). Qed.
Lemma lem4349004 {A : Type'} (_49556 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49556.
Proof. exact (EQ_MP (@lem4348266 A s' _49556) (@lem4348265 A _49556 s' h1)). Qed.
Lemma lem4349018 {A : Type'} (_49559 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49559.
Proof. exact (EQ_MP (@lem4348275 A s _49559) (@lem4348274 A _49559 s h1)). Qed.
Lemma lem4349028 {A : Type'} (_49560 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49560.
Proof. exact (EQ_MP (@lem4348278 A s' _49560) (@lem4348277 A _49560 s' h1)). Qed.
Lemma lem4349042 {A : Type'} (_49563 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49563.
Proof. exact (EQ_MP (@lem4348287 A s _49563) (@lem4348286 A _49563 s h1)). Qed.
Lemma lem4349052 {A : Type'} (_49564 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49564.
Proof. exact (EQ_MP (@lem4348290 A s' _49564) (@lem4348289 A _49564 s' h1)). Qed.
Lemma lem4349066 {B : Type'} (_49567 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49567.
Proof. exact (EQ_MP (@lem4348299 B t _49567) (@lem4348298 B _49567 t h1)). Qed.
Lemma lem4349076 {A : Type'} (_49568 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49568.
Proof. exact (EQ_MP (@lem4348302 A s' _49568) (@lem4348301 A _49568 s' h1)). Qed.
Lemma lem4349090 {B : Type'} (_49571 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49571.
Proof. exact (EQ_MP (@lem4348311 B t _49571) (@lem4348310 B _49571 t h1)). Qed.
Lemma lem4349100 {A : Type'} (_49572 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49572.
Proof. exact (EQ_MP (@lem4348314 A s' _49572) (@lem4348313 A _49572 s' h1)). Qed.
Lemma lem4349114 {B : Type'} (_49575 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49575.
Proof. exact (EQ_MP (@lem4348323 B t _49575) (@lem4348322 B _49575 t h1)). Qed.
Lemma lem4349126 {B : Type'} (_49577 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49577.
Proof. exact (EQ_MP (@lem4348329 B t _49577) (@lem4348328 B _49577 t h1)). Qed.
Lemma lem4349138 {B : Type'} (_49579 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49579.
Proof. exact (EQ_MP (@lem4348335 B t _49579) (@lem4348334 B _49579 t h1)). Qed.
Lemma lem4349148 {A : Type'} (_49580 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49580.
Proof. exact (EQ_MP (@lem4348338 A s' _49580) (@lem4348337 A _49580 s' h1)). Qed.
Lemma lem4349166 {A B : Type'} (_49583 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 A s s' _49583.
Proof. exact (EQ_MP (@lem4348347 A s s' _49583) (@lem4348346 A B _49583 s s' t t' h1)). Qed.
Lemma lem4349176 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term99 A s' x''.
Proof. exact (proj2 (@lem4344015 A s s' x'' h1)). Qed.
Lemma lem4349182 {A : Type'} (_49585 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49585.
Proof. exact (EQ_MP (@lem4348353 A s' _49585) (@lem4348352 A _49585 s' h1)). Qed.
Lemma lem4349204 {A : Type'} (_49588 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49588.
Proof. exact (EQ_MP (@lem4348362 A s' _49588) (@lem4348361 A _49588 s' h1)). Qed.
Lemma lem4349226 {A : Type'} (_49591 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49591.
Proof. exact (EQ_MP (@lem4348371 A s' _49591) (@lem4348370 A _49591 s' h1)). Qed.
Lemma lem4349260 {A B : Type'} (_49596 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 B t t' _49596.
Proof. exact (EQ_MP (@lem4348386 B t t' _49596) (@lem4348385 A B _49596 s s' t t' h1)). Qed.
Lemma lem4349264 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term99 B t' x'''.
Proof. exact (proj2 (@lem4344033 B t t' x''' h1)). Qed.
Lemma lem4349270 {A : Type'} (_49597 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49597.
Proof. exact (EQ_MP (@lem4348389 A s' _49597) (@lem4348388 A _49597 s' h1)). Qed.
Lemma lem4349292 {A : Type'} (_49600 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49600.
Proof. exact (EQ_MP (@lem4348398 A s' _49600) (@lem4348397 A _49600 s' h1)). Qed.
Lemma lem4349298 {A B : Type'} (_49601 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 A s s' _49601.
Proof. exact (EQ_MP (@lem4348401 A s s' _49601) (@lem4348400 A B _49601 s s' t t' h1)). Qed.
Lemma lem4349314 {A : Type'} (_49603 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49603.
Proof. exact (EQ_MP (@lem4348407 A s' _49603) (@lem4348406 A _49603 s' h1)). Qed.
Lemma lem4349338 {A : Type'} (_49607 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49607.
Proof. exact (EQ_MP (@lem4348419 A s _49607) (@lem4348418 A _49607 s h1)). Qed.
Lemma lem4349350 {A : Type'} (_49609 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49609.
Proof. exact (EQ_MP (@lem4348425 A s _49609) (@lem4348424 A _49609 s h1)). Qed.
Lemma lem4349362 {A : Type'} (_49611 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49611.
Proof. exact (EQ_MP (@lem4348431 A s _49611) (@lem4348430 A _49611 s h1)). Qed.
Lemma lem4349372 {B : Type'} (_49612 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49612.
Proof. exact (EQ_MP (@lem4348434 B t' _49612) (@lem4348433 B _49612 t' h1)). Qed.
Lemma lem4349386 {A : Type'} (_49615 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49615.
Proof. exact (EQ_MP (@lem4348443 A s _49615) (@lem4348442 A _49615 s h1)). Qed.
Lemma lem4349396 {B : Type'} (_49616 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49616.
Proof. exact (EQ_MP (@lem4348446 B t' _49616) (@lem4348445 B _49616 t' h1)). Qed.
Lemma lem4349410 {A : Type'} (_49619 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49619.
Proof. exact (EQ_MP (@lem4348455 A s _49619) (@lem4348454 A _49619 s h1)). Qed.
Lemma lem4349420 {B : Type'} (_49620 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49620.
Proof. exact (EQ_MP (@lem4348458 B t' _49620) (@lem4348457 B _49620 t' h1)). Qed.
Lemma lem4349434 {B : Type'} (_49623 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49623.
Proof. exact (EQ_MP (@lem4348467 B t _49623) (@lem4348466 B _49623 t h1)). Qed.
Lemma lem4349444 {B : Type'} (_49624 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49624.
Proof. exact (EQ_MP (@lem4348470 B t' _49624) (@lem4348469 B _49624 t' h1)). Qed.
Lemma lem4349458 {B : Type'} (_49627 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49627.
Proof. exact (EQ_MP (@lem4348479 B t _49627) (@lem4348478 B _49627 t h1)). Qed.
Lemma lem4349468 {B : Type'} (_49628 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49628.
Proof. exact (EQ_MP (@lem4348482 B t' _49628) (@lem4348481 B _49628 t' h1)). Qed.
Lemma lem4349482 {B : Type'} (_49631 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49631.
Proof. exact (EQ_MP (@lem4348491 B t _49631) (@lem4348490 B _49631 t h1)). Qed.
Lemma lem4349494 {B : Type'} (_49633 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49633.
Proof. exact (EQ_MP (@lem4348497 B t _49633) (@lem4348496 B _49633 t h1)). Qed.
Lemma lem4349506 {B : Type'} (_49635 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49635.
Proof. exact (EQ_MP (@lem4348503 B t _49635) (@lem4348502 B _49635 t h1)). Qed.
Lemma lem4349516 {B : Type'} (_49636 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49636.
Proof. exact (EQ_MP (@lem4348506 B t' _49636) (@lem4348505 B _49636 t' h1)). Qed.
Lemma lem4349534 {A B : Type'} (_49639 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 A s s' _49639.
Proof. exact (EQ_MP (@lem4348515 A s s' _49639) (@lem4348514 A B _49639 s s' t t' h1)). Qed.
Lemma lem4349544 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term99 A s' x''.
Proof. exact (proj2 (@lem4344137 A s s' x'' h1)). Qed.
Lemma lem4349550 {B : Type'} (_49641 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49641.
Proof. exact (EQ_MP (@lem4348521 B t' _49641) (@lem4348520 B _49641 t' h1)). Qed.
Lemma lem4349572 {B : Type'} (_49644 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49644.
Proof. exact (EQ_MP (@lem4348530 B t' _49644) (@lem4348529 B _49644 t' h1)). Qed.
Lemma lem4349584 {A B : Type'} (_49646 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 B t t' _49646.
Proof. exact (EQ_MP (@lem4348536 B t t' _49646) (@lem4348535 A B _49646 s s' t t' h1)). Qed.
Lemma lem4349594 {B : Type'} (_49647 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49647.
Proof. exact (EQ_MP (@lem4348539 B t' _49647) (@lem4348538 B _49647 t' h1)). Qed.
Lemma lem4349628 {A B : Type'} (_49652 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 B t t' _49652.
Proof. exact (EQ_MP (@lem4348554 B t t' _49652) (@lem4348553 A B _49652 s s' t t' h1)). Qed.
Lemma lem4349632 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term99 B t' x'''.
Proof. exact (proj2 (@lem4344155 B t t' x''' h1)). Qed.
Lemma lem4349638 {B : Type'} (_49653 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49653.
Proof. exact (EQ_MP (@lem4348557 B t' _49653) (@lem4348556 B _49653 t' h1)). Qed.
Lemma lem4349660 {B : Type'} (_49656 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49656.
Proof. exact (EQ_MP (@lem4348566 B t' _49656) (@lem4348565 B _49656 t' h1)). Qed.
Lemma lem4349682 {B : Type'} (_49659 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49659.
Proof. exact (EQ_MP (@lem4348575 B t' _49659) (@lem4348574 B _49659 t' h1)). Qed.
Lemma lem4349716 {A : Type'} (_49664 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49664.
Proof. exact (EQ_MP (@lem4348590 A s _49664) (@lem4348589 A _49664 s h1)). Qed.
Lemma lem4349738 {A : Type'} (_49667 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49667.
Proof. exact (EQ_MP (@lem4348599 A s _49667) (@lem4348598 A _49667 s h1)). Qed.
Lemma lem4349760 {A : Type'} (_49670 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49670.
Proof. exact (EQ_MP (@lem4348608 A s _49670) (@lem4348607 A _49670 s h1)). Qed.
Lemma lem4349774 {A B : Type'} (_49671 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 A s' s _49671.
Proof. exact (EQ_MP (@lem4348611 A s' s _49671) (@lem4348610 A B _49671 s' s t' t h1)). Qed.
Lemma lem4349786 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term99 A s x''.
Proof. exact (proj2 (@lem4344180 A s' s x'' h1)). Qed.
Lemma lem4349804 {A : Type'} (_49676 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49676.
Proof. exact (EQ_MP (@lem4348626 A s _49676) (@lem4348625 A _49676 s h1)). Qed.
Lemma lem4349818 {A B : Type'} (_49677 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 A s' s _49677.
Proof. exact (EQ_MP (@lem4348629 A s' s _49677) (@lem4348628 A B _49677 s' s t' t h1)). Qed.
Lemma lem4349826 {A : Type'} (_49679 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49679.
Proof. exact (EQ_MP (@lem4348635 A s _49679) (@lem4348634 A _49679 s h1)). Qed.
Lemma lem4349848 {A : Type'} (_49682 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49682.
Proof. exact (EQ_MP (@lem4348644 A s _49682) (@lem4348643 A _49682 s h1)). Qed.
Lemma lem4349868 {A B : Type'} (_49684 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 B t' t _49684.
Proof. exact (EQ_MP (@lem4348650 B t' t _49684) (@lem4348649 A B _49684 s' s t' t h1)). Qed.
Lemma lem4349874 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term99 B t x'''.
Proof. exact (proj2 (@lem4344198 B t' t x''' h1)). Qed.
Lemma lem4349892 {B : Type'} (_49688 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49688.
Proof. exact (EQ_MP (@lem4348662 B t _49688) (@lem4348661 B _49688 t h1)). Qed.
Lemma lem4349912 {A B : Type'} (_49690 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 B t' t _49690.
Proof. exact (EQ_MP (@lem4348668 B t' t _49690) (@lem4348667 A B _49690 s' s t' t h1)). Qed.
Lemma lem4349914 {B : Type'} (_49691 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49691.
Proof. exact (EQ_MP (@lem4348671 B t _49691) (@lem4348670 B _49691 t h1)). Qed.
Lemma lem4349936 {B : Type'} (_49694 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49694.
Proof. exact (EQ_MP (@lem4348680 B t _49694) (@lem4348679 B _49694 t h1)). Qed.
Lemma lem4349950 {A B : Type'} (_49695 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 A s' s _49695.
Proof. exact (EQ_MP (@lem4348683 A s' s _49695) (@lem4348682 A B _49695 s' s t' t h1)). Qed.
Lemma lem4349962 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term99 A s x''.
Proof. exact (proj2 (@lem4344220 A s' s x'' h1)). Qed.
Lemma lem4349980 {B : Type'} (_49700 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49700.
Proof. exact (EQ_MP (@lem4348698 B t _49700) (@lem4348697 B _49700 t h1)). Qed.
Lemma lem4350002 {B : Type'} (_49703 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49703.
Proof. exact (EQ_MP (@lem4348707 B t _49703) (@lem4348706 B _49703 t h1)). Qed.
Lemma lem4350024 {B : Type'} (_49706 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49706.
Proof. exact (EQ_MP (@lem4348716 B t _49706) (@lem4348715 B _49706 t h1)). Qed.
Lemma lem4350044 {A B : Type'} (_49708 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 B t' t _49708.
Proof. exact (EQ_MP (@lem4348722 B t' t _49708) (@lem4348721 A B _49708 s' s t' t h1)). Qed.
Lemma lem4350050 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term99 B t x'''.
Proof. exact (proj2 (@lem4344238 B t' t x''' h1)). Qed.
Lemma lem4350072 {A B : Type'} (_49712 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 A s s' _49712.
Proof. exact (EQ_MP (@lem4348734 A s s' _49712) (@lem4348733 A B _49712 s s' t t' h1)). Qed.
Lemma lem4350082 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term99 A s' x''.
Proof. exact (proj2 (@lem4344259 A s s' x'' h1)). Qed.
Lemma lem4350104 {A B : Type'} (_49716 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 A s s' _49716.
Proof. exact (EQ_MP (@lem4348746 A s s' _49716) (@lem4348745 A B _49716 s s' t t' h1)). Qed.
Lemma lem4350114 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term99 A s' x''.
Proof. exact (proj2 (@lem4344259 A s s' x'' h1)). Qed.
Lemma lem4350124 {A B : Type'} (_49718 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 A s' s _49718.
Proof. exact (EQ_MP (@lem4348752 A s' s _49718) (@lem4348751 A B _49718 s' s t' t h1)). Qed.
Lemma lem4350146 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term99 A s x''.
Proof. exact (proj2 (@lem4344260 A s' s x'' h1)). Qed.
Lemma lem4350156 {A B : Type'} (_49722 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 A s' s _49722.
Proof. exact (EQ_MP (@lem4348764 A s' s _49722) (@lem4348763 A B _49722 s' s t' t h1)). Qed.
Lemma lem4350178 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term99 A s x''.
Proof. exact (proj2 (@lem4344260 A s' s x'' h1)). Qed.
Lemma lem4350206 {A B : Type'} (_49729 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 B t t' _49729.
Proof. exact (EQ_MP (@lem4348785 B t t' _49729) (@lem4348784 A B _49729 s s' t t' h1)). Qed.
Lemma lem4350210 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term99 B t' x'''.
Proof. exact (proj2 (@lem4344277 B t t' x''' h1)). Qed.
Lemma lem4350238 {A B : Type'} (_49733 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term163 B t t' _49733.
Proof. exact (EQ_MP (@lem4348797 B t t' _49733) (@lem4348796 A B _49733 s s' t t' h1)). Qed.
Lemma lem4350242 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term99 B t' x'''.
Proof. exact (proj2 (@lem4344277 B t t' x''' h1)). Qed.
Lemma lem4350258 {A B : Type'} (_49735 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 B t' t _49735.
Proof. exact (EQ_MP (@lem4348803 B t' t _49735) (@lem4348802 A B _49735 s' s t' t h1)). Qed.
Lemma lem4350274 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term99 B t x'''.
Proof. exact (proj2 (@lem4344278 B t' t x''' h1)). Qed.
Lemma lem4350290 {A B : Type'} (_49739 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term163 B t' t _49739.
Proof. exact (EQ_MP (@lem4348815 B t' t _49739) (@lem4348814 A B _49739 s' s t' t h1)). Qed.
Lemma lem4350306 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term99 B t x'''.
Proof. exact (proj2 (@lem4344278 B t' t x''' h1)). Qed.
Lemma lem4350314 {A : Type'} (_49743 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49743.
Proof. exact (EQ_MP (@lem4348827 A s _49743) (@lem4348826 A _49743 s h1)). Qed.
Lemma lem4350326 {A : Type'} (_49745 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49745.
Proof. exact (EQ_MP (@lem4348833 A s _49745) (@lem4348832 A _49745 s h1)). Qed.
Lemma lem4350336 {A : Type'} (_49746 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49746.
Proof. exact (EQ_MP (@lem4348836 A s' _49746) (@lem4348835 A _49746 s' h1)). Qed.
Lemma lem4350348 {A : Type'} (_49748 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49748.
Proof. exact (EQ_MP (@lem4348842 A s' _49748) (@lem4348841 A _49748 s' h1)). Qed.
Lemma lem4350362 {B : Type'} (_49751 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49751.
Proof. exact (EQ_MP (@lem4348851 B t _49751) (@lem4348850 B _49751 t h1)). Qed.
Lemma lem4350374 {B : Type'} (_49753 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49753.
Proof. exact (EQ_MP (@lem4348857 B t _49753) (@lem4348856 B _49753 t h1)). Qed.
Lemma lem4350384 {A : Type'} (_49754 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49754.
Proof. exact (EQ_MP (@lem4348860 A s' _49754) (@lem4348859 A _49754 s' h1)). Qed.
Lemma lem4350396 {A : Type'} (_49756 : A) (s' : A -> Prop) (h1 : term102 A s') : term99 A s' _49756.
Proof. exact (EQ_MP (@lem4348866 A s' _49756) (@lem4348865 A _49756 s' h1)). Qed.
Lemma lem4350410 {A : Type'} (_49759 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49759.
Proof. exact (EQ_MP (@lem4348875 A s _49759) (@lem4348874 A _49759 s h1)). Qed.
Lemma lem4350422 {A : Type'} (_49761 : A) (s : A -> Prop) (h1 : term102 A s) : term99 A s _49761.
Proof. exact (EQ_MP (@lem4348881 A s _49761) (@lem4348880 A _49761 s h1)). Qed.
Lemma lem4350432 {B : Type'} (_49762 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49762.
Proof. exact (EQ_MP (@lem4348884 B t' _49762) (@lem4348883 B _49762 t' h1)). Qed.
Lemma lem4350444 {B : Type'} (_49764 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49764.
Proof. exact (EQ_MP (@lem4348890 B t' _49764) (@lem4348889 B _49764 t' h1)). Qed.
Lemma lem4350458 {B : Type'} (_49767 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49767.
Proof. exact (EQ_MP (@lem4348899 B t _49767) (@lem4348898 B _49767 t h1)). Qed.
Lemma lem4350470 {B : Type'} (_49769 : B) (t : B -> Prop) (h1 : term102 B t) : term99 B t _49769.
Proof. exact (EQ_MP (@lem4348905 B t _49769) (@lem4348904 B _49769 t h1)). Qed.
Lemma lem4350480 {B : Type'} (_49770 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49770.
Proof. exact (EQ_MP (@lem4348908 B t' _49770) (@lem4348907 B _49770 t' h1)). Qed.
Lemma lem4350492 {B : Type'} (_49772 : B) (t' : B -> Prop) (h1 : term102 B t') : term99 B t' _49772.
Proof. exact (EQ_MP (@lem4348914 B t' _49772) (@lem4348913 B _49772 t' h1)). Qed.
Lemma lem4350520 {A B : Type'} (_49776 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term163 A s s' _49776.
Proof. exact (EQ_MP (@lem4348926 A s s' _49776) (@lem4348925 A B _49776 s' s t' t h1)). Qed.
Lemma lem4350534 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term99 A s' x''.
Proof. exact (proj2 (@lem4344407 A s s' x'' h1)). Qed.
Lemma lem4350540 {A B : Type'} (_49778 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term163 B t t' _49778.
Proof. exact (EQ_MP (@lem4348932 B t t' _49778) (@lem4348931 A B _49778 s' s t' t h1)). Qed.
Lemma lem4350566 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term99 B t' x'''.
Proof. exact (proj2 (@lem4344408 B t t' x''' h1)). Qed.
Lemma lem4350590 {A B : Type'} (_49785 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term163 A s' s _49785.
Proof. exact (EQ_MP (@lem4348953 A s' s _49785) (@lem4348952 A B _49785 s' s t' t h1)). Qed.
Lemma lem4350598 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term99 A s x''.
Proof. exact (proj2 (@lem4344417 A s' s x'' h1)). Qed.
Lemma lem4350610 {A B : Type'} (_49787 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term163 B t' t _49787.
Proof. exact (EQ_MP (@lem4348959 B t' t _49787) (@lem4348958 A B _49787 s' s t' t h1)). Qed.
Lemma lem4350630 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term99 B t x'''.
Proof. exact (proj2 (@lem4344418 B t' t x''' h1)). Qed.
Lemma lem4350632 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4343939 A B s x t x' h1)). Qed.
Lemma lem4350633 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4350632 A B s x t x' h1). Qed.
Lemma lem4350635 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350636 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4350635 (s x)). Qed.
Lemma lem4350637 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4350636 A s x) (@lem4350633 A B s x t x' h1)). Qed.
Lemma lem4350640 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350642 {A : Type'} (s : A -> Prop) (_49551 : A) : (term99 A s _49551) = (term98 A s _49551).
Proof. exact (@lem4350640 (s _49551)). Qed.
Lemma lem4350645 {A : Type'} (_49551 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49551.
Proof. exact (EQ_MP (@lem4350642 A s _49551) (@lem4348970 A _49551 s h1)). Qed.
Lemma lem4350646 {A : Type'} (_49551 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49551.
Proof. exact (@lem4350645 A _49551 s h1). Qed.
Lemma lem4350647 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4350646 A x s h1). Qed.
Lemma lem4350650 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350647 A x s h1 (@lem4350637 A B s x t x' h2)). Qed.
Lemma lem4350651 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350650 A B s x t x' h1 h2). Qed.
Lemma lem4350653 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350654 : term764 = False.
Proof. exact (@lem4350653 False). Qed.
Lemma lem4350655 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4350654) (@lem4350651 A B s x t x' h1 h2)). Qed.
Lemma lem4350657 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4343935 A s s' x'' h1)). Qed.
Lemma lem4350658 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4350657 A s s' x'' h1). Qed.
Lemma lem4350660 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350661 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4350660 (s x'')). Qed.
Lemma lem4350662 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4350661 A s x'') (@lem4350658 A s s' x'' h1)). Qed.
Lemma lem4350665 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350667 {A : Type'} (s : A -> Prop) (_49553 : A) : (term99 A s _49553) = (term98 A s _49553).
Proof. exact (@lem4350665 (s _49553)). Qed.
Lemma lem4350670 {A : Type'} (_49553 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49553.
Proof. exact (EQ_MP (@lem4350667 A s _49553) (@lem4348982 A _49553 s h1)). Qed.
Lemma lem4350671 {A : Type'} (_49553 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49553.
Proof. exact (@lem4350670 A _49553 s h1). Qed.
Lemma lem4350672 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x''.
Proof. exact (@lem4350671 A x'' s h1). Qed.
Lemma lem4350675 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4350672 A x'' s h1 (@lem4350662 A s s' x'' h2)). Qed.
Lemma lem4350676 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4350675 A s s' x'' h1 h2). Qed.
Lemma lem4350678 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350679 : term764 = False.
Proof. exact (@lem4350678 False). Qed.
Lemma lem4350680 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4350679) (@lem4350676 A s s' x'' h1 h2)). Qed.
Lemma lem4350682 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4343947 A B s x t x' h1)). Qed.
Lemma lem4350683 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4350682 A B s x t x' h1). Qed.
Lemma lem4350685 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350686 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4350685 (s x)). Qed.
Lemma lem4350687 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4350686 A s x) (@lem4350683 A B s x t x' h1)). Qed.
Lemma lem4350690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350692 {A : Type'} (s : A -> Prop) (_49555 : A) : (term99 A s _49555) = (term98 A s _49555).
Proof. exact (@lem4350690 (s _49555)). Qed.
Lemma lem4350695 {A : Type'} (_49555 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49555.
Proof. exact (EQ_MP (@lem4350692 A s _49555) (@lem4348994 A _49555 s h1)). Qed.
Lemma lem4350696 {A : Type'} (_49555 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49555.
Proof. exact (@lem4350695 A _49555 s h1). Qed.
Lemma lem4350697 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4350696 A x s h1). Qed.
Lemma lem4350700 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350697 A x s h1 (@lem4350687 A B s x t x' h2)). Qed.
Lemma lem4350701 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350700 A B s x t x' h1 h2). Qed.
Lemma lem4350703 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350704 : term764 = False.
Proof. exact (@lem4350703 False). Qed.
Lemma lem4350705 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4350704) (@lem4350701 A B s x t x' h1 h2)). Qed.
Lemma lem4350707 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4343948 A B s' x t' x' h1)). Qed.
Lemma lem4350708 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4350707 A B s' x t' x' h1). Qed.
Lemma lem4350710 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350711 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4350710 (s' x)). Qed.
Lemma lem4350712 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4350711 A s' x) (@lem4350708 A B s' x t' x' h1)). Qed.
Lemma lem4350715 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350717 {A : Type'} (s' : A -> Prop) (_49556 : A) : (term99 A s' _49556) = (term98 A s' _49556).
Proof. exact (@lem4350715 (s' _49556)). Qed.
Lemma lem4350720 {A : Type'} (_49556 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49556.
Proof. exact (EQ_MP (@lem4350717 A s' _49556) (@lem4349004 A _49556 s' h1)). Qed.
Lemma lem4350721 {A : Type'} (_49556 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49556.
Proof. exact (@lem4350720 A _49556 s' h1). Qed.
Lemma lem4350722 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4350721 A x s' h1). Qed.
Lemma lem4350725 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4350722 A x s' h1 (@lem4350712 A B s' x t' x' h2)). Qed.
Lemma lem4350726 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350725 A B s' x t' x' h1 h2). Qed.
Lemma lem4350728 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350729 : term764 = False.
Proof. exact (@lem4350728 False). Qed.
Lemma lem4350730 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4350729) (@lem4350726 A B s' x t' x' h1 h2)). Qed.
Lemma lem4350732 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4343957 A B s x t x' h1)). Qed.
Lemma lem4350733 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4350732 A B s x t x' h1). Qed.
Lemma lem4350735 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350736 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4350735 (s x)). Qed.
Lemma lem4350737 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4350736 A s x) (@lem4350733 A B s x t x' h1)). Qed.
Lemma lem4350740 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350742 {A : Type'} (s : A -> Prop) (_49559 : A) : (term99 A s _49559) = (term98 A s _49559).
Proof. exact (@lem4350740 (s _49559)). Qed.
Lemma lem4350745 {A : Type'} (_49559 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49559.
Proof. exact (EQ_MP (@lem4350742 A s _49559) (@lem4349018 A _49559 s h1)). Qed.
Lemma lem4350746 {A : Type'} (_49559 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49559.
Proof. exact (@lem4350745 A _49559 s h1). Qed.
Lemma lem4350747 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4350746 A x s h1). Qed.
Lemma lem4350750 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350747 A x s h1 (@lem4350737 A B s x t x' h2)). Qed.
Lemma lem4350751 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350750 A B s x t x' h1 h2). Qed.
Lemma lem4350753 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350754 : term764 = False.
Proof. exact (@lem4350753 False). Qed.
Lemma lem4350755 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4350754) (@lem4350751 A B s x t x' h1 h2)). Qed.
Lemma lem4350757 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4343958 A B s' x t' x' h1)). Qed.
Lemma lem4350758 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4350757 A B s' x t' x' h1). Qed.
Lemma lem4350760 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350761 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4350760 (s' x)). Qed.
Lemma lem4350762 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4350761 A s' x) (@lem4350758 A B s' x t' x' h1)). Qed.
Lemma lem4350765 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350767 {A : Type'} (s' : A -> Prop) (_49560 : A) : (term99 A s' _49560) = (term98 A s' _49560).
Proof. exact (@lem4350765 (s' _49560)). Qed.
Lemma lem4350770 {A : Type'} (_49560 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49560.
Proof. exact (EQ_MP (@lem4350767 A s' _49560) (@lem4349028 A _49560 s' h1)). Qed.
Lemma lem4350771 {A : Type'} (_49560 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49560.
Proof. exact (@lem4350770 A _49560 s' h1). Qed.
Lemma lem4350772 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4350771 A x s' h1). Qed.
Lemma lem4350775 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4350772 A x s' h1 (@lem4350762 A B s' x t' x' h2)). Qed.
Lemma lem4350776 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350775 A B s' x t' x' h1 h2). Qed.
Lemma lem4350778 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350779 : term764 = False.
Proof. exact (@lem4350778 False). Qed.
Lemma lem4350780 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4350779) (@lem4350776 A B s' x t' x' h1 h2)). Qed.
Lemma lem4350782 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4343965 A B s x t x' h1)). Qed.
Lemma lem4350783 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4350782 A B s x t x' h1). Qed.
Lemma lem4350785 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350786 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4350785 (s x)). Qed.
Lemma lem4350787 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4350786 A s x) (@lem4350783 A B s x t x' h1)). Qed.
Lemma lem4350790 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350792 {A : Type'} (s : A -> Prop) (_49563 : A) : (term99 A s _49563) = (term98 A s _49563).
Proof. exact (@lem4350790 (s _49563)). Qed.
Lemma lem4350795 {A : Type'} (_49563 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49563.
Proof. exact (EQ_MP (@lem4350792 A s _49563) (@lem4349042 A _49563 s h1)). Qed.
Lemma lem4350796 {A : Type'} (_49563 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49563.
Proof. exact (@lem4350795 A _49563 s h1). Qed.
Lemma lem4350797 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4350796 A x s h1). Qed.
Lemma lem4350800 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350797 A x s h1 (@lem4350787 A B s x t x' h2)). Qed.
Lemma lem4350801 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350800 A B s x t x' h1 h2). Qed.
Lemma lem4350803 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350804 : term764 = False.
Proof. exact (@lem4350803 False). Qed.
Lemma lem4350805 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4350804) (@lem4350801 A B s x t x' h1 h2)). Qed.
Lemma lem4350807 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4343966 A B s' x t' x' h1)). Qed.
Lemma lem4350808 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4350807 A B s' x t' x' h1). Qed.
Lemma lem4350810 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350811 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4350810 (s' x)). Qed.
Lemma lem4350812 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4350811 A s' x) (@lem4350808 A B s' x t' x' h1)). Qed.
Lemma lem4350815 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350817 {A : Type'} (s' : A -> Prop) (_49564 : A) : (term99 A s' _49564) = (term98 A s' _49564).
Proof. exact (@lem4350815 (s' _49564)). Qed.
Lemma lem4350820 {A : Type'} (_49564 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49564.
Proof. exact (EQ_MP (@lem4350817 A s' _49564) (@lem4349052 A _49564 s' h1)). Qed.
Lemma lem4350821 {A : Type'} (_49564 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49564.
Proof. exact (@lem4350820 A _49564 s' h1). Qed.
Lemma lem4350822 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4350821 A x s' h1). Qed.
Lemma lem4350825 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4350822 A x s' h1 (@lem4350812 A B s' x t' x' h2)). Qed.
Lemma lem4350826 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350825 A B s' x t' x' h1 h2). Qed.
Lemma lem4350828 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350829 : term764 = False.
Proof. exact (@lem4350828 False). Qed.
Lemma lem4350830 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4350829) (@lem4350826 A B s' x t' x' h1 h2)). Qed.
Lemma lem4350832 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4343979 A B s x t x' h1)). Qed.
Lemma lem4350833 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4350832 A B s x t x' h1). Qed.
Lemma lem4350835 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350836 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4350835 (t x')). Qed.
Lemma lem4350837 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4350836 B t x') (@lem4350833 A B s x t x' h1)). Qed.
Lemma lem4350840 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350842 {B : Type'} (t : B -> Prop) (_49567 : B) : (term99 B t _49567) = (term98 B t _49567).
Proof. exact (@lem4350840 (t _49567)). Qed.
Lemma lem4350845 {B : Type'} (_49567 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49567.
Proof. exact (EQ_MP (@lem4350842 B t _49567) (@lem4349066 B _49567 t h1)). Qed.
Lemma lem4350846 {B : Type'} (_49567 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49567.
Proof. exact (@lem4350845 B _49567 t h1). Qed.
Lemma lem4350847 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4350846 B x' t h1). Qed.
Lemma lem4350850 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350847 B x' t h1 (@lem4350837 A B s x t x' h2)). Qed.
Lemma lem4350851 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350850 A B s x t x' h1 h2). Qed.
Lemma lem4350853 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350854 : term764 = False.
Proof. exact (@lem4350853 False). Qed.
Lemma lem4350855 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4350854) (@lem4350851 A B s x t x' h1 h2)). Qed.
Lemma lem4350857 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4343980 A B s' x t' x' h1)). Qed.
Lemma lem4350858 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4350857 A B s' x t' x' h1). Qed.
Lemma lem4350860 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350861 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4350860 (s' x)). Qed.
Lemma lem4350862 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4350861 A s' x) (@lem4350858 A B s' x t' x' h1)). Qed.
Lemma lem4350865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350867 {A : Type'} (s' : A -> Prop) (_49568 : A) : (term99 A s' _49568) = (term98 A s' _49568).
Proof. exact (@lem4350865 (s' _49568)). Qed.
Lemma lem4350870 {A : Type'} (_49568 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49568.
Proof. exact (EQ_MP (@lem4350867 A s' _49568) (@lem4349076 A _49568 s' h1)). Qed.
Lemma lem4350871 {A : Type'} (_49568 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49568.
Proof. exact (@lem4350870 A _49568 s' h1). Qed.
Lemma lem4350872 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4350871 A x s' h1). Qed.
Lemma lem4350875 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4350872 A x s' h1 (@lem4350862 A B s' x t' x' h2)). Qed.
Lemma lem4350876 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350875 A B s' x t' x' h1 h2). Qed.
Lemma lem4350878 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350879 : term764 = False.
Proof. exact (@lem4350878 False). Qed.
Lemma lem4350880 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4350879) (@lem4350876 A B s' x t' x' h1 h2)). Qed.
Lemma lem4350882 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4343987 A B s x t x' h1)). Qed.
Lemma lem4350883 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4350882 A B s x t x' h1). Qed.
Lemma lem4350885 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350886 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4350885 (t x')). Qed.
Lemma lem4350887 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4350886 B t x') (@lem4350883 A B s x t x' h1)). Qed.
Lemma lem4350890 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350892 {B : Type'} (t : B -> Prop) (_49571 : B) : (term99 B t _49571) = (term98 B t _49571).
Proof. exact (@lem4350890 (t _49571)). Qed.
Lemma lem4350895 {B : Type'} (_49571 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49571.
Proof. exact (EQ_MP (@lem4350892 B t _49571) (@lem4349090 B _49571 t h1)). Qed.
Lemma lem4350896 {B : Type'} (_49571 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49571.
Proof. exact (@lem4350895 B _49571 t h1). Qed.
Lemma lem4350897 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4350896 B x' t h1). Qed.
Lemma lem4350900 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350897 B x' t h1 (@lem4350887 A B s x t x' h2)). Qed.
Lemma lem4350901 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350900 A B s x t x' h1 h2). Qed.
Lemma lem4350903 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350904 : term764 = False.
Proof. exact (@lem4350903 False). Qed.
Lemma lem4350905 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4350904) (@lem4350901 A B s x t x' h1 h2)). Qed.
Lemma lem4350907 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4343988 A B s' x t' x' h1)). Qed.
Lemma lem4350908 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4350907 A B s' x t' x' h1). Qed.
Lemma lem4350910 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350911 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4350910 (s' x)). Qed.
Lemma lem4350912 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4350911 A s' x) (@lem4350908 A B s' x t' x' h1)). Qed.
Lemma lem4350915 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350917 {A : Type'} (s' : A -> Prop) (_49572 : A) : (term99 A s' _49572) = (term98 A s' _49572).
Proof. exact (@lem4350915 (s' _49572)). Qed.
Lemma lem4350920 {A : Type'} (_49572 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49572.
Proof. exact (EQ_MP (@lem4350917 A s' _49572) (@lem4349100 A _49572 s' h1)). Qed.
Lemma lem4350921 {A : Type'} (_49572 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49572.
Proof. exact (@lem4350920 A _49572 s' h1). Qed.
Lemma lem4350922 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4350921 A x s' h1). Qed.
Lemma lem4350925 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4350922 A x s' h1 (@lem4350912 A B s' x t' x' h2)). Qed.
Lemma lem4350926 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350925 A B s' x t' x' h1 h2). Qed.
Lemma lem4350928 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350929 : term764 = False.
Proof. exact (@lem4350928 False). Qed.
Lemma lem4350930 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4350929) (@lem4350926 A B s' x t' x' h1 h2)). Qed.
Lemma lem4350932 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4343997 A B s x t x' h1)). Qed.
Lemma lem4350933 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4350932 A B s x t x' h1). Qed.
Lemma lem4350935 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350936 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4350935 (t x')). Qed.
Lemma lem4350937 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4350936 B t x') (@lem4350933 A B s x t x' h1)). Qed.
Lemma lem4350940 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350942 {B : Type'} (t : B -> Prop) (_49575 : B) : (term99 B t _49575) = (term98 B t _49575).
Proof. exact (@lem4350940 (t _49575)). Qed.
Lemma lem4350945 {B : Type'} (_49575 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49575.
Proof. exact (EQ_MP (@lem4350942 B t _49575) (@lem4349114 B _49575 t h1)). Qed.
Lemma lem4350946 {B : Type'} (_49575 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49575.
Proof. exact (@lem4350945 B _49575 t h1). Qed.
Lemma lem4350947 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4350946 B x' t h1). Qed.
Lemma lem4350950 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350947 B x' t h1 (@lem4350937 A B s x t x' h2)). Qed.
Lemma lem4350951 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4350950 A B s x t x' h1 h2). Qed.
Lemma lem4350953 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350954 : term764 = False.
Proof. exact (@lem4350953 False). Qed.
Lemma lem4350955 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4350954) (@lem4350951 A B s x t x' h1 h2)). Qed.
Lemma lem4350957 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4343993 B t t' x''' h1)). Qed.
Lemma lem4350958 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4350957 B t t' x''' h1). Qed.
Lemma lem4350960 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350961 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4350960 (t x''')). Qed.
Lemma lem4350962 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4350961 B t x''') (@lem4350958 B t t' x''' h1)). Qed.
Lemma lem4350965 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350967 {B : Type'} (t : B -> Prop) (_49577 : B) : (term99 B t _49577) = (term98 B t _49577).
Proof. exact (@lem4350965 (t _49577)). Qed.
Lemma lem4350970 {B : Type'} (_49577 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49577.
Proof. exact (EQ_MP (@lem4350967 B t _49577) (@lem4349126 B _49577 t h1)). Qed.
Lemma lem4350971 {B : Type'} (_49577 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49577.
Proof. exact (@lem4350970 B _49577 t h1). Qed.
Lemma lem4350972 {B : Type'} (x''' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'''.
Proof. exact (@lem4350971 B x''' t h1). Qed.
Lemma lem4350975 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4350972 B x''' t h1 (@lem4350962 B t t' x''' h2)). Qed.
Lemma lem4350976 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4350975 B t t' x''' h1 h2). Qed.
Lemma lem4350978 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350979 : term764 = False.
Proof. exact (@lem4350978 False). Qed.
Lemma lem4350980 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4350979) (@lem4350976 B t t' x''' h1 h2)). Qed.
Lemma lem4350982 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344005 A B s x t x' h1)). Qed.
Lemma lem4350983 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4350982 A B s x t x' h1). Qed.
Lemma lem4350985 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4350986 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4350985 (t x')). Qed.
Lemma lem4350987 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4350986 B t x') (@lem4350983 A B s x t x' h1)). Qed.
Lemma lem4350990 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4350992 {B : Type'} (t : B -> Prop) (_49579 : B) : (term99 B t _49579) = (term98 B t _49579).
Proof. exact (@lem4350990 (t _49579)). Qed.
Lemma lem4350995 {B : Type'} (_49579 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49579.
Proof. exact (EQ_MP (@lem4350992 B t _49579) (@lem4349138 B _49579 t h1)). Qed.
Lemma lem4350996 {B : Type'} (_49579 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49579.
Proof. exact (@lem4350995 B _49579 t h1). Qed.
Lemma lem4350997 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4350996 B x' t h1). Qed.
Lemma lem4351000 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4350997 B x' t h1 (@lem4350987 A B s x t x' h2)). Qed.
Lemma lem4351001 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351000 A B s x t x' h1 h2). Qed.
Lemma lem4351003 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351004 : term764 = False.
Proof. exact (@lem4351003 False). Qed.
Lemma lem4351005 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351004) (@lem4351001 A B s x t x' h1 h2)). Qed.
Lemma lem4351007 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4344006 A B s' x t' x' h1)). Qed.
Lemma lem4351008 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4351007 A B s' x t' x' h1). Qed.
Lemma lem4351010 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351011 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4351010 (s' x)). Qed.
Lemma lem4351012 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4351011 A s' x) (@lem4351008 A B s' x t' x' h1)). Qed.
Lemma lem4351015 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351017 {A : Type'} (s' : A -> Prop) (_49580 : A) : (term99 A s' _49580) = (term98 A s' _49580).
Proof. exact (@lem4351015 (s' _49580)). Qed.
Lemma lem4351020 {A : Type'} (_49580 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49580.
Proof. exact (EQ_MP (@lem4351017 A s' _49580) (@lem4349148 A _49580 s' h1)). Qed.
Lemma lem4351021 {A : Type'} (_49580 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49580.
Proof. exact (@lem4351020 A _49580 s' h1). Qed.
Lemma lem4351022 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4351021 A x s' h1). Qed.
Lemma lem4351025 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351022 A x s' h1 (@lem4351012 A B s' x t' x' h2)). Qed.
Lemma lem4351026 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351025 A B s' x t' x' h1 h2). Qed.
Lemma lem4351028 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351029 : term764 = False.
Proof. exact (@lem4351028 False). Qed.
Lemma lem4351030 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351029) (@lem4351026 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351032 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344015 A s s' x'' h1)). Qed.
Lemma lem4351033 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4351032 A s s' x'' h1). Qed.
Lemma lem4351035 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351036 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4351035 (s x'')). Qed.
Lemma lem4351037 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4351036 A s x'') (@lem4351033 A s s' x'' h1)). Qed.
Lemma lem4351043 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4351044 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : (term163 A s s' _49583) = (term765 A s' s _49583).
Proof. exact (@lem4351043 (s' _49583) (term99 A s _49583)). Qed.
Lemma lem4351050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4351051 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : (term766 A s s' _49583) = (term767 A s' s _49583).
Proof. exact (MK_COMB (@lem4351050) (@lem4351044 A s' s _49583)). Qed.
Lemma lem4351057 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : (term765 A s' s _49583) = (term765 A s' s _49583).
Proof. exact (eq_refl (term765 A s' s _49583)). Qed.
Lemma lem4351058 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : ((term163 A s s' _49583) = (term765 A s' s _49583)) = ((term765 A s' s _49583) = (term765 A s' s _49583)).
Proof. exact (MK_COMB (@lem4351051 A s' s _49583) (@lem4351057 A s' s _49583)). Qed.
Lemma lem4351060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4351061 (x : Prop) : (x = x) = True.
Proof. exact (@lem4351060 Prop x). Qed.
Lemma lem4351062 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : ((term765 A s' s _49583) = (term765 A s' s _49583)) = True.
Proof. exact (@lem4351061 (term765 A s' s _49583)). Qed.
Lemma lem4351063 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : ((term163 A s s' _49583) = (term765 A s' s _49583)) = True.
Proof. exact (TRANS (@lem4351058 A s' s _49583) (@lem4351062 A s' s _49583)). Qed.
Lemma lem4351064 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : True = ((term163 A s s' _49583) = (term765 A s' s _49583)).
Proof. exact (SYM (@lem4351063 A s' s _49583)). Qed.
Lemma lem4351065 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49583 : A) : (term163 A s s' _49583) = (term765 A s' s _49583).
Proof. exact (EQ_MP (@lem4351064 A s' s _49583) (@lem0)). Qed.
Lemma lem4351066 {A B : Type'} (_49583 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 A s' s _49583.
Proof. exact (EQ_MP (@lem4351065 A s' s _49583) (@lem4349166 A B _49583 s s' t t' h1)). Qed.
Lemma lem4351068 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4351069 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49583 : A) : (term765 A s' s _49583) = (term769 A s s' _49583).
Proof. exact (@lem4351068 (term99 A s _49583) (s' _49583)). Qed.
Lemma lem4351071 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4351072 {A : Type'} (s : A -> Prop) (_49583 : A) : (term151 A s _49583) = (s _49583).
Proof. exact (@lem4351071 (s _49583)). Qed.
Lemma lem4351073 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4351074 {A : Type'} (s : A -> Prop) (_49583 : A) : (term770 A s _49583) = (term96 A s _49583).
Proof. exact (MK_COMB (@lem4351073) (@lem4351072 A s _49583)). Qed.
Lemma lem4351075 {A : Type'} (s' : A -> Prop) (_49583 : A) : (s' _49583) = (s' _49583).
Proof. exact (eq_refl (s' _49583)). Qed.
Lemma lem4351076 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49583 : A) : (term769 A s s' _49583) = (term114 A s s' _49583).
Proof. exact (MK_COMB (@lem4351074 A s _49583) (@lem4351075 A s' _49583)). Qed.
Lemma lem4351077 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49583 : A) : (term765 A s' s _49583) = (term114 A s s' _49583).
Proof. exact (TRANS (@lem4351069 A s s' _49583) (@lem4351076 A s s' _49583)). Qed.
Lemma lem4351080 {A B : Type'} (_49583 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49583.
Proof. exact (EQ_MP (@lem4351077 A s s' _49583) (@lem4351066 A B _49583 s s' t t' h1)). Qed.
Lemma lem4351081 {A B : Type'} (_49583 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49583.
Proof. exact (@lem4351080 A B _49583 s s' t t' h1). Qed.
Lemma lem4351082 {A B : Type'} (x'' : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' x''.
Proof. exact (@lem4351081 A B x'' s s' t t' h1). Qed.
Lemma lem4351085 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (@lem4351082 A B x'' s s' t t' h1 (@lem4351037 A s s' x'' h2)). Qed.
Lemma lem4351086 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4351085 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4351088 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351089 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4351088 (s' x'')). Qed.
Lemma lem4351090 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (EQ_MP (@lem4351089 A s' x'') (@lem4351086 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4351093 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351095 {A : Type'} (s' : A -> Prop) (x'' : A) : (term99 A s' x'') = (term98 A s' x'').
Proof. exact (@lem4351093 (s' x'')). Qed.
Lemma lem4351098 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term98 A s' x''.
Proof. exact (EQ_MP (@lem4351095 A s' x'') (@lem4349176 A s s' x'' h1)). Qed.
Lemma lem4351101 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4351098 A s s' x'' h2 (@lem4351090 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4351102 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4351101 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4351104 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351105 : term764 = False.
Proof. exact (@lem4351104 False). Qed.
Lemma lem4351106 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4351105) (@lem4351102 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4351108 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4344020 A B s' x t' x' h1)). Qed.
Lemma lem4351109 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4351108 A B s' x t' x' h1). Qed.
Lemma lem4351111 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351112 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4351111 (s' x)). Qed.
Lemma lem4351113 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4351112 A s' x) (@lem4351109 A B s' x t' x' h1)). Qed.
Lemma lem4351116 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351118 {A : Type'} (s' : A -> Prop) (_49585 : A) : (term99 A s' _49585) = (term98 A s' _49585).
Proof. exact (@lem4351116 (s' _49585)). Qed.
Lemma lem4351121 {A : Type'} (_49585 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49585.
Proof. exact (EQ_MP (@lem4351118 A s' _49585) (@lem4349182 A _49585 s' h1)). Qed.
Lemma lem4351122 {A : Type'} (_49585 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49585.
Proof. exact (@lem4351121 A _49585 s' h1). Qed.
Lemma lem4351123 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4351122 A x s' h1). Qed.
Lemma lem4351126 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351123 A x s' h1 (@lem4351113 A B s' x t' x' h2)). Qed.
Lemma lem4351127 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351126 A B s' x t' x' h1 h2). Qed.
Lemma lem4351129 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351130 : term764 = False.
Proof. exact (@lem4351129 False). Qed.
Lemma lem4351131 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351130) (@lem4351127 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351133 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344016 A s' s x'' h1)). Qed.
Lemma lem4351134 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4351133 A s' s x'' h1). Qed.
Lemma lem4351136 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351137 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4351136 (s' x'')). Qed.
Lemma lem4351138 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4351137 A s' x'') (@lem4351134 A s' s x'' h1)). Qed.
Lemma lem4351141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351143 {A : Type'} (s' : A -> Prop) (_49588 : A) : (term99 A s' _49588) = (term98 A s' _49588).
Proof. exact (@lem4351141 (s' _49588)). Qed.
Lemma lem4351146 {A : Type'} (_49588 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49588.
Proof. exact (EQ_MP (@lem4351143 A s' _49588) (@lem4349204 A _49588 s' h1)). Qed.
Lemma lem4351147 {A : Type'} (_49588 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49588.
Proof. exact (@lem4351146 A _49588 s' h1). Qed.
Lemma lem4351148 {A : Type'} (x'' : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x''.
Proof. exact (@lem4351147 A x'' s' h1). Qed.
Lemma lem4351151 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (@lem4351148 A x'' s' h1 (@lem4351138 A s' s x'' h2)). Qed.
Lemma lem4351152 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4351151 A s' s x'' h1 h2). Qed.
Lemma lem4351154 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351155 : term764 = False.
Proof. exact (@lem4351154 False). Qed.
Lemma lem4351156 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4351155) (@lem4351152 A s' s x'' h1 h2)). Qed.
Lemma lem4351158 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4344028 A B s' x t' x' h1)). Qed.
Lemma lem4351159 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4351158 A B s' x t' x' h1). Qed.
Lemma lem4351161 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351162 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4351161 (s' x)). Qed.
Lemma lem4351163 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4351162 A s' x) (@lem4351159 A B s' x t' x' h1)). Qed.
Lemma lem4351166 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351168 {A : Type'} (s' : A -> Prop) (_49591 : A) : (term99 A s' _49591) = (term98 A s' _49591).
Proof. exact (@lem4351166 (s' _49591)). Qed.
Lemma lem4351171 {A : Type'} (_49591 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49591.
Proof. exact (EQ_MP (@lem4351168 A s' _49591) (@lem4349226 A _49591 s' h1)). Qed.
Lemma lem4351172 {A : Type'} (_49591 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49591.
Proof. exact (@lem4351171 A _49591 s' h1). Qed.
Lemma lem4351173 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4351172 A x s' h1). Qed.
Lemma lem4351176 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351173 A x s' h1 (@lem4351163 A B s' x t' x' h2)). Qed.
Lemma lem4351177 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351176 A B s' x t' x' h1 h2). Qed.
Lemma lem4351179 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351180 : term764 = False.
Proof. exact (@lem4351179 False). Qed.
Lemma lem4351181 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351180) (@lem4351177 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351183 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344033 B t t' x''' h1)). Qed.
Lemma lem4351184 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4351183 B t t' x''' h1). Qed.
Lemma lem4351186 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351187 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4351186 (t x''')). Qed.
Lemma lem4351188 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4351187 B t x''') (@lem4351184 B t t' x''' h1)). Qed.
Lemma lem4351194 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4351195 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : (term163 B t t' _49596) = (term765 B t' t _49596).
Proof. exact (@lem4351194 (t' _49596) (term99 B t _49596)). Qed.
Lemma lem4351201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4351202 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : (term766 B t t' _49596) = (term767 B t' t _49596).
Proof. exact (MK_COMB (@lem4351201) (@lem4351195 B t' t _49596)). Qed.
Lemma lem4351208 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : (term765 B t' t _49596) = (term765 B t' t _49596).
Proof. exact (eq_refl (term765 B t' t _49596)). Qed.
Lemma lem4351209 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : ((term163 B t t' _49596) = (term765 B t' t _49596)) = ((term765 B t' t _49596) = (term765 B t' t _49596)).
Proof. exact (MK_COMB (@lem4351202 B t' t _49596) (@lem4351208 B t' t _49596)). Qed.
Lemma lem4351211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4351212 (x : Prop) : (x = x) = True.
Proof. exact (@lem4351211 Prop x). Qed.
Lemma lem4351213 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : ((term765 B t' t _49596) = (term765 B t' t _49596)) = True.
Proof. exact (@lem4351212 (term765 B t' t _49596)). Qed.
Lemma lem4351214 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : ((term163 B t t' _49596) = (term765 B t' t _49596)) = True.
Proof. exact (TRANS (@lem4351209 B t' t _49596) (@lem4351213 B t' t _49596)). Qed.
Lemma lem4351215 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : True = ((term163 B t t' _49596) = (term765 B t' t _49596)).
Proof. exact (SYM (@lem4351214 B t' t _49596)). Qed.
Lemma lem4351216 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49596 : B) : (term163 B t t' _49596) = (term765 B t' t _49596).
Proof. exact (EQ_MP (@lem4351215 B t' t _49596) (@lem0)). Qed.
Lemma lem4351217 {A B : Type'} (_49596 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 B t' t _49596.
Proof. exact (EQ_MP (@lem4351216 B t' t _49596) (@lem4349260 A B _49596 s s' t t' h1)). Qed.
Lemma lem4351219 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4351220 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49596 : B) : (term765 B t' t _49596) = (term769 B t t' _49596).
Proof. exact (@lem4351219 (term99 B t _49596) (t' _49596)). Qed.
Lemma lem4351222 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4351223 {B : Type'} (t : B -> Prop) (_49596 : B) : (term151 B t _49596) = (t _49596).
Proof. exact (@lem4351222 (t _49596)). Qed.
Lemma lem4351224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4351225 {B : Type'} (t : B -> Prop) (_49596 : B) : (term770 B t _49596) = (term96 B t _49596).
Proof. exact (MK_COMB (@lem4351224) (@lem4351223 B t _49596)). Qed.
Lemma lem4351226 {B : Type'} (t' : B -> Prop) (_49596 : B) : (t' _49596) = (t' _49596).
Proof. exact (eq_refl (t' _49596)). Qed.
Lemma lem4351227 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49596 : B) : (term769 B t t' _49596) = (term114 B t t' _49596).
Proof. exact (MK_COMB (@lem4351225 B t _49596) (@lem4351226 B t' _49596)). Qed.
Lemma lem4351228 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49596 : B) : (term765 B t' t _49596) = (term114 B t t' _49596).
Proof. exact (TRANS (@lem4351220 B t t' _49596) (@lem4351227 B t t' _49596)). Qed.
Lemma lem4351231 {A B : Type'} (_49596 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49596.
Proof. exact (EQ_MP (@lem4351228 B t t' _49596) (@lem4351217 A B _49596 s s' t t' h1)). Qed.
Lemma lem4351232 {A B : Type'} (_49596 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49596.
Proof. exact (@lem4351231 A B _49596 s s' t t' h1). Qed.
Lemma lem4351233 {A B : Type'} (x''' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' x'''.
Proof. exact (@lem4351232 A B x''' s s' t t' h1). Qed.
Lemma lem4351236 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (@lem4351233 A B x''' s s' t t' h1 (@lem4351188 B t t' x''' h2)). Qed.
Lemma lem4351237 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4351236 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4351239 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351240 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4351239 (t' x''')). Qed.
Lemma lem4351241 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (EQ_MP (@lem4351240 B t' x''') (@lem4351237 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4351244 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351246 {B : Type'} (t' : B -> Prop) (x''' : B) : (term99 B t' x''') = (term98 B t' x''').
Proof. exact (@lem4351244 (t' x''')). Qed.
Lemma lem4351249 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term98 B t' x'''.
Proof. exact (EQ_MP (@lem4351246 B t' x''') (@lem4349264 B t t' x''' h1)). Qed.
Lemma lem4351252 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4351249 B t t' x''' h2 (@lem4351241 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4351253 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4351252 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4351255 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351256 : term764 = False.
Proof. exact (@lem4351255 False). Qed.
Lemma lem4351257 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4351256) (@lem4351253 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4351259 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4344038 A B s' x t' x' h1)). Qed.
Lemma lem4351260 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4351259 A B s' x t' x' h1). Qed.
Lemma lem4351262 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351263 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4351262 (s' x)). Qed.
Lemma lem4351264 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4351263 A s' x) (@lem4351260 A B s' x t' x' h1)). Qed.
Lemma lem4351267 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351269 {A : Type'} (s' : A -> Prop) (_49597 : A) : (term99 A s' _49597) = (term98 A s' _49597).
Proof. exact (@lem4351267 (s' _49597)). Qed.
Lemma lem4351272 {A : Type'} (_49597 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49597.
Proof. exact (EQ_MP (@lem4351269 A s' _49597) (@lem4349270 A _49597 s' h1)). Qed.
Lemma lem4351273 {A : Type'} (_49597 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49597.
Proof. exact (@lem4351272 A _49597 s' h1). Qed.
Lemma lem4351274 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4351273 A x s' h1). Qed.
Lemma lem4351277 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351274 A x s' h1 (@lem4351264 A B s' x t' x' h2)). Qed.
Lemma lem4351278 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351277 A B s' x t' x' h1 h2). Qed.
Lemma lem4351280 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351281 : term764 = False.
Proof. exact (@lem4351280 False). Qed.
Lemma lem4351282 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351281) (@lem4351278 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351284 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344045 A B s x t x' h1)). Qed.
Lemma lem4351285 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4351284 A B s x t x' h1). Qed.
Lemma lem4351287 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351288 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4351287 (s x)). Qed.
Lemma lem4351289 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4351288 A s x) (@lem4351285 A B s x t x' h1)). Qed.
Lemma lem4351295 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4351296 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : (term163 A s s' _49601) = (term765 A s' s _49601).
Proof. exact (@lem4351295 (s' _49601) (term99 A s _49601)). Qed.
Lemma lem4351302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4351303 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : (term766 A s s' _49601) = (term767 A s' s _49601).
Proof. exact (MK_COMB (@lem4351302) (@lem4351296 A s' s _49601)). Qed.
Lemma lem4351309 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : (term765 A s' s _49601) = (term765 A s' s _49601).
Proof. exact (eq_refl (term765 A s' s _49601)). Qed.
Lemma lem4351310 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : ((term163 A s s' _49601) = (term765 A s' s _49601)) = ((term765 A s' s _49601) = (term765 A s' s _49601)).
Proof. exact (MK_COMB (@lem4351303 A s' s _49601) (@lem4351309 A s' s _49601)). Qed.
Lemma lem4351312 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4351313 (x : Prop) : (x = x) = True.
Proof. exact (@lem4351312 Prop x). Qed.
Lemma lem4351314 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : ((term765 A s' s _49601) = (term765 A s' s _49601)) = True.
Proof. exact (@lem4351313 (term765 A s' s _49601)). Qed.
Lemma lem4351315 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : ((term163 A s s' _49601) = (term765 A s' s _49601)) = True.
Proof. exact (TRANS (@lem4351310 A s' s _49601) (@lem4351314 A s' s _49601)). Qed.
Lemma lem4351316 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : True = ((term163 A s s' _49601) = (term765 A s' s _49601)).
Proof. exact (SYM (@lem4351315 A s' s _49601)). Qed.
Lemma lem4351317 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49601 : A) : (term163 A s s' _49601) = (term765 A s' s _49601).
Proof. exact (EQ_MP (@lem4351316 A s' s _49601) (@lem0)). Qed.
Lemma lem4351318 {A B : Type'} (_49601 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 A s' s _49601.
Proof. exact (EQ_MP (@lem4351317 A s' s _49601) (@lem4349298 A B _49601 s s' t t' h1)). Qed.
Lemma lem4351320 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4351321 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49601 : A) : (term765 A s' s _49601) = (term769 A s s' _49601).
Proof. exact (@lem4351320 (term99 A s _49601) (s' _49601)). Qed.
Lemma lem4351323 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4351324 {A : Type'} (s : A -> Prop) (_49601 : A) : (term151 A s _49601) = (s _49601).
Proof. exact (@lem4351323 (s _49601)). Qed.
Lemma lem4351325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4351326 {A : Type'} (s : A -> Prop) (_49601 : A) : (term770 A s _49601) = (term96 A s _49601).
Proof. exact (MK_COMB (@lem4351325) (@lem4351324 A s _49601)). Qed.
Lemma lem4351327 {A : Type'} (s' : A -> Prop) (_49601 : A) : (s' _49601) = (s' _49601).
Proof. exact (eq_refl (s' _49601)). Qed.
Lemma lem4351328 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49601 : A) : (term769 A s s' _49601) = (term114 A s s' _49601).
Proof. exact (MK_COMB (@lem4351326 A s _49601) (@lem4351327 A s' _49601)). Qed.
Lemma lem4351329 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49601 : A) : (term765 A s' s _49601) = (term114 A s s' _49601).
Proof. exact (TRANS (@lem4351321 A s s' _49601) (@lem4351328 A s s' _49601)). Qed.
Lemma lem4351332 {A B : Type'} (_49601 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49601.
Proof. exact (EQ_MP (@lem4351329 A s s' _49601) (@lem4351318 A B _49601 s s' t t' h1)). Qed.
Lemma lem4351333 {A B : Type'} (_49601 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49601.
Proof. exact (@lem4351332 A B _49601 s s' t t' h1). Qed.
Lemma lem4351334 {A B : Type'} (x : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' x.
Proof. exact (@lem4351333 A B x s s' t t' h1). Qed.
Lemma lem4351337 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term179 A B s s' t t') (h2 : term267 A B s x t x') : s' x.
Proof. exact (@lem4351334 A B x s s' t t' h1 (@lem4351289 A B s x t x' h2)). Qed.
Lemma lem4351338 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term179 A B s s' t t') (h2 : term267 A B s x t x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4351337 A B s' t' s x t x' h1 h2). Qed.
Lemma lem4351340 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351341 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4351340 (s' x)). Qed.
Lemma lem4351342 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term179 A B s s' t t') (h2 : term267 A B s x t x') : s' x.
Proof. exact (EQ_MP (@lem4351341 A s' x) (@lem4351338 A B s' t' s x t x' h1 h2)). Qed.
Lemma lem4351345 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351347 {A : Type'} (s' : A -> Prop) (_49600 : A) : (term99 A s' _49600) = (term98 A s' _49600).
Proof. exact (@lem4351345 (s' _49600)). Qed.
Lemma lem4351350 {A : Type'} (_49600 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49600.
Proof. exact (EQ_MP (@lem4351347 A s' _49600) (@lem4349292 A _49600 s' h1)). Qed.
Lemma lem4351351 {A : Type'} (_49600 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49600.
Proof. exact (@lem4351350 A _49600 s' h1). Qed.
Lemma lem4351352 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4351351 A x s' h1). Qed.
Lemma lem4351355 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : False.
Proof. exact (@lem4351352 A x s' h1 (@lem4351342 A B s' t' s x t x' h2 h3)). Qed.
Lemma lem4351356 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351355 A B s' t' s x t x' h1 h2 h3). Qed.
Lemma lem4351358 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351359 : term764 = False.
Proof. exact (@lem4351358 False). Qed.
Lemma lem4351360 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351359) (@lem4351356 A B s' t' s x t x' h1 h2 h3)). Qed.
Lemma lem4351362 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4344046 A B s' x t' x' h1)). Qed.
Lemma lem4351363 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4351362 A B s' x t' x' h1). Qed.
Lemma lem4351365 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351366 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4351365 (s' x)). Qed.
Lemma lem4351367 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4351366 A s' x) (@lem4351363 A B s' x t' x' h1)). Qed.
Lemma lem4351370 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351372 {A : Type'} (s' : A -> Prop) (_49603 : A) : (term99 A s' _49603) = (term98 A s' _49603).
Proof. exact (@lem4351370 (s' _49603)). Qed.
Lemma lem4351375 {A : Type'} (_49603 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49603.
Proof. exact (EQ_MP (@lem4351372 A s' _49603) (@lem4349314 A _49603 s' h1)). Qed.
Lemma lem4351376 {A : Type'} (_49603 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49603.
Proof. exact (@lem4351375 A _49603 s' h1). Qed.
Lemma lem4351377 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4351376 A x s' h1). Qed.
Lemma lem4351380 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351377 A x s' h1 (@lem4351367 A B s' x t' x' h2)). Qed.
Lemma lem4351381 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351380 A B s' x t' x' h1 h2). Qed.
Lemma lem4351383 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351384 : term764 = False.
Proof. exact (@lem4351383 False). Qed.
Lemma lem4351385 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351384) (@lem4351381 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351387 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344061 A B s x t x' h1)). Qed.
Lemma lem4351388 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4351387 A B s x t x' h1). Qed.
Lemma lem4351390 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351391 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4351390 (s x)). Qed.
Lemma lem4351392 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4351391 A s x) (@lem4351388 A B s x t x' h1)). Qed.
Lemma lem4351395 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351397 {A : Type'} (s : A -> Prop) (_49607 : A) : (term99 A s _49607) = (term98 A s _49607).
Proof. exact (@lem4351395 (s _49607)). Qed.
Lemma lem4351400 {A : Type'} (_49607 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49607.
Proof. exact (EQ_MP (@lem4351397 A s _49607) (@lem4349338 A _49607 s h1)). Qed.
Lemma lem4351401 {A : Type'} (_49607 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49607.
Proof. exact (@lem4351400 A _49607 s h1). Qed.
Lemma lem4351402 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4351401 A x s h1). Qed.
Lemma lem4351405 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351402 A x s h1 (@lem4351392 A B s x t x' h2)). Qed.
Lemma lem4351406 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351405 A B s x t x' h1 h2). Qed.
Lemma lem4351408 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351409 : term764 = False.
Proof. exact (@lem4351408 False). Qed.
Lemma lem4351410 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351409) (@lem4351406 A B s x t x' h1 h2)). Qed.
Lemma lem4351412 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344057 A s s' x'' h1)). Qed.
Lemma lem4351413 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4351412 A s s' x'' h1). Qed.
Lemma lem4351415 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351416 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4351415 (s x'')). Qed.
Lemma lem4351417 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4351416 A s x'') (@lem4351413 A s s' x'' h1)). Qed.
Lemma lem4351420 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351422 {A : Type'} (s : A -> Prop) (_49609 : A) : (term99 A s _49609) = (term98 A s _49609).
Proof. exact (@lem4351420 (s _49609)). Qed.
Lemma lem4351425 {A : Type'} (_49609 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49609.
Proof. exact (EQ_MP (@lem4351422 A s _49609) (@lem4349350 A _49609 s h1)). Qed.
Lemma lem4351426 {A : Type'} (_49609 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49609.
Proof. exact (@lem4351425 A _49609 s h1). Qed.
Lemma lem4351427 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x''.
Proof. exact (@lem4351426 A x'' s h1). Qed.
Lemma lem4351430 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4351427 A x'' s h1 (@lem4351417 A s s' x'' h2)). Qed.
Lemma lem4351431 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4351430 A s s' x'' h1 h2). Qed.
Lemma lem4351433 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351434 : term764 = False.
Proof. exact (@lem4351433 False). Qed.
Lemma lem4351435 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4351434) (@lem4351431 A s s' x'' h1 h2)). Qed.
Lemma lem4351437 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344069 A B s x t x' h1)). Qed.
Lemma lem4351438 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4351437 A B s x t x' h1). Qed.
Lemma lem4351440 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351441 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4351440 (s x)). Qed.
Lemma lem4351442 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4351441 A s x) (@lem4351438 A B s x t x' h1)). Qed.
Lemma lem4351445 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351447 {A : Type'} (s : A -> Prop) (_49611 : A) : (term99 A s _49611) = (term98 A s _49611).
Proof. exact (@lem4351445 (s _49611)). Qed.
Lemma lem4351450 {A : Type'} (_49611 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49611.
Proof. exact (EQ_MP (@lem4351447 A s _49611) (@lem4349362 A _49611 s h1)). Qed.
Lemma lem4351451 {A : Type'} (_49611 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49611.
Proof. exact (@lem4351450 A _49611 s h1). Qed.
Lemma lem4351452 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4351451 A x s h1). Qed.
Lemma lem4351455 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351452 A x s h1 (@lem4351442 A B s x t x' h2)). Qed.
Lemma lem4351456 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351455 A B s x t x' h1 h2). Qed.
Lemma lem4351458 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351459 : term764 = False.
Proof. exact (@lem4351458 False). Qed.
Lemma lem4351460 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351459) (@lem4351456 A B s x t x' h1 h2)). Qed.
Lemma lem4351462 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344070 A B s' x t' x' h1)). Qed.
Lemma lem4351463 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351462 A B s' x t' x' h1). Qed.
Lemma lem4351465 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351466 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351465 (t' x')). Qed.
Lemma lem4351467 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351466 B t' x') (@lem4351463 A B s' x t' x' h1)). Qed.
Lemma lem4351470 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351472 {B : Type'} (t' : B -> Prop) (_49612 : B) : (term99 B t' _49612) = (term98 B t' _49612).
Proof. exact (@lem4351470 (t' _49612)). Qed.
Lemma lem4351475 {B : Type'} (_49612 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49612.
Proof. exact (EQ_MP (@lem4351472 B t' _49612) (@lem4349372 B _49612 t' h1)). Qed.
Lemma lem4351476 {B : Type'} (_49612 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49612.
Proof. exact (@lem4351475 B _49612 t' h1). Qed.
Lemma lem4351477 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351476 B x' t' h1). Qed.
Lemma lem4351480 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351477 B x' t' h1 (@lem4351467 A B s' x t' x' h2)). Qed.
Lemma lem4351481 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351480 A B s' x t' x' h1 h2). Qed.
Lemma lem4351483 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351484 : term764 = False.
Proof. exact (@lem4351483 False). Qed.
Lemma lem4351485 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351484) (@lem4351481 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351487 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344079 A B s x t x' h1)). Qed.
Lemma lem4351488 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4351487 A B s x t x' h1). Qed.
Lemma lem4351490 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351491 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4351490 (s x)). Qed.
Lemma lem4351492 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4351491 A s x) (@lem4351488 A B s x t x' h1)). Qed.
Lemma lem4351495 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351497 {A : Type'} (s : A -> Prop) (_49615 : A) : (term99 A s _49615) = (term98 A s _49615).
Proof. exact (@lem4351495 (s _49615)). Qed.
Lemma lem4351500 {A : Type'} (_49615 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49615.
Proof. exact (EQ_MP (@lem4351497 A s _49615) (@lem4349386 A _49615 s h1)). Qed.
Lemma lem4351501 {A : Type'} (_49615 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49615.
Proof. exact (@lem4351500 A _49615 s h1). Qed.
Lemma lem4351502 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4351501 A x s h1). Qed.
Lemma lem4351505 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351502 A x s h1 (@lem4351492 A B s x t x' h2)). Qed.
Lemma lem4351506 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351505 A B s x t x' h1 h2). Qed.
Lemma lem4351508 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351509 : term764 = False.
Proof. exact (@lem4351508 False). Qed.
Lemma lem4351510 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351509) (@lem4351506 A B s x t x' h1 h2)). Qed.
Lemma lem4351512 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344080 A B s' x t' x' h1)). Qed.
Lemma lem4351513 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351512 A B s' x t' x' h1). Qed.
Lemma lem4351515 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351516 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351515 (t' x')). Qed.
Lemma lem4351517 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351516 B t' x') (@lem4351513 A B s' x t' x' h1)). Qed.
Lemma lem4351520 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351522 {B : Type'} (t' : B -> Prop) (_49616 : B) : (term99 B t' _49616) = (term98 B t' _49616).
Proof. exact (@lem4351520 (t' _49616)). Qed.
Lemma lem4351525 {B : Type'} (_49616 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49616.
Proof. exact (EQ_MP (@lem4351522 B t' _49616) (@lem4349396 B _49616 t' h1)). Qed.
Lemma lem4351526 {B : Type'} (_49616 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49616.
Proof. exact (@lem4351525 B _49616 t' h1). Qed.
Lemma lem4351527 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351526 B x' t' h1). Qed.
Lemma lem4351530 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351527 B x' t' h1 (@lem4351517 A B s' x t' x' h2)). Qed.
Lemma lem4351531 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351530 A B s' x t' x' h1 h2). Qed.
Lemma lem4351533 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351534 : term764 = False.
Proof. exact (@lem4351533 False). Qed.
Lemma lem4351535 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351534) (@lem4351531 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351537 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344087 A B s x t x' h1)). Qed.
Lemma lem4351538 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4351537 A B s x t x' h1). Qed.
Lemma lem4351540 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351541 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4351540 (s x)). Qed.
Lemma lem4351542 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4351541 A s x) (@lem4351538 A B s x t x' h1)). Qed.
Lemma lem4351545 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351547 {A : Type'} (s : A -> Prop) (_49619 : A) : (term99 A s _49619) = (term98 A s _49619).
Proof. exact (@lem4351545 (s _49619)). Qed.
Lemma lem4351550 {A : Type'} (_49619 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49619.
Proof. exact (EQ_MP (@lem4351547 A s _49619) (@lem4349410 A _49619 s h1)). Qed.
Lemma lem4351551 {A : Type'} (_49619 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49619.
Proof. exact (@lem4351550 A _49619 s h1). Qed.
Lemma lem4351552 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4351551 A x s h1). Qed.
Lemma lem4351555 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351552 A x s h1 (@lem4351542 A B s x t x' h2)). Qed.
Lemma lem4351556 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351555 A B s x t x' h1 h2). Qed.
Lemma lem4351558 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351559 : term764 = False.
Proof. exact (@lem4351558 False). Qed.
Lemma lem4351560 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351559) (@lem4351556 A B s x t x' h1 h2)). Qed.
Lemma lem4351562 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344088 A B s' x t' x' h1)). Qed.
Lemma lem4351563 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351562 A B s' x t' x' h1). Qed.
Lemma lem4351565 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351566 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351565 (t' x')). Qed.
Lemma lem4351567 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351566 B t' x') (@lem4351563 A B s' x t' x' h1)). Qed.
Lemma lem4351570 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351572 {B : Type'} (t' : B -> Prop) (_49620 : B) : (term99 B t' _49620) = (term98 B t' _49620).
Proof. exact (@lem4351570 (t' _49620)). Qed.
Lemma lem4351575 {B : Type'} (_49620 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49620.
Proof. exact (EQ_MP (@lem4351572 B t' _49620) (@lem4349420 B _49620 t' h1)). Qed.
Lemma lem4351576 {B : Type'} (_49620 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49620.
Proof. exact (@lem4351575 B _49620 t' h1). Qed.
Lemma lem4351577 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351576 B x' t' h1). Qed.
Lemma lem4351580 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351577 B x' t' h1 (@lem4351567 A B s' x t' x' h2)). Qed.
Lemma lem4351581 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351580 A B s' x t' x' h1 h2). Qed.
Lemma lem4351583 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351584 : term764 = False.
Proof. exact (@lem4351583 False). Qed.
Lemma lem4351585 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351584) (@lem4351581 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351587 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344101 A B s x t x' h1)). Qed.
Lemma lem4351588 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4351587 A B s x t x' h1). Qed.
Lemma lem4351590 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351591 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4351590 (t x')). Qed.
Lemma lem4351592 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4351591 B t x') (@lem4351588 A B s x t x' h1)). Qed.
Lemma lem4351595 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351597 {B : Type'} (t : B -> Prop) (_49623 : B) : (term99 B t _49623) = (term98 B t _49623).
Proof. exact (@lem4351595 (t _49623)). Qed.
Lemma lem4351600 {B : Type'} (_49623 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49623.
Proof. exact (EQ_MP (@lem4351597 B t _49623) (@lem4349434 B _49623 t h1)). Qed.
Lemma lem4351601 {B : Type'} (_49623 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49623.
Proof. exact (@lem4351600 B _49623 t h1). Qed.
Lemma lem4351602 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4351601 B x' t h1). Qed.
Lemma lem4351605 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351602 B x' t h1 (@lem4351592 A B s x t x' h2)). Qed.
Lemma lem4351606 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351605 A B s x t x' h1 h2). Qed.
Lemma lem4351608 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351609 : term764 = False.
Proof. exact (@lem4351608 False). Qed.
Lemma lem4351610 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351609) (@lem4351606 A B s x t x' h1 h2)). Qed.
Lemma lem4351612 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344102 A B s' x t' x' h1)). Qed.
Lemma lem4351613 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351612 A B s' x t' x' h1). Qed.
Lemma lem4351615 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351616 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351615 (t' x')). Qed.
Lemma lem4351617 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351616 B t' x') (@lem4351613 A B s' x t' x' h1)). Qed.
Lemma lem4351620 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351622 {B : Type'} (t' : B -> Prop) (_49624 : B) : (term99 B t' _49624) = (term98 B t' _49624).
Proof. exact (@lem4351620 (t' _49624)). Qed.
Lemma lem4351625 {B : Type'} (_49624 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49624.
Proof. exact (EQ_MP (@lem4351622 B t' _49624) (@lem4349444 B _49624 t' h1)). Qed.
Lemma lem4351626 {B : Type'} (_49624 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49624.
Proof. exact (@lem4351625 B _49624 t' h1). Qed.
Lemma lem4351627 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351626 B x' t' h1). Qed.
Lemma lem4351630 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351627 B x' t' h1 (@lem4351617 A B s' x t' x' h2)). Qed.
Lemma lem4351631 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351630 A B s' x t' x' h1 h2). Qed.
Lemma lem4351633 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351634 : term764 = False.
Proof. exact (@lem4351633 False). Qed.
Lemma lem4351635 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351634) (@lem4351631 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351637 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344109 A B s x t x' h1)). Qed.
Lemma lem4351638 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4351637 A B s x t x' h1). Qed.
Lemma lem4351640 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351641 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4351640 (t x')). Qed.
Lemma lem4351642 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4351641 B t x') (@lem4351638 A B s x t x' h1)). Qed.
Lemma lem4351645 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351647 {B : Type'} (t : B -> Prop) (_49627 : B) : (term99 B t _49627) = (term98 B t _49627).
Proof. exact (@lem4351645 (t _49627)). Qed.
Lemma lem4351650 {B : Type'} (_49627 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49627.
Proof. exact (EQ_MP (@lem4351647 B t _49627) (@lem4349458 B _49627 t h1)). Qed.
Lemma lem4351651 {B : Type'} (_49627 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49627.
Proof. exact (@lem4351650 B _49627 t h1). Qed.
Lemma lem4351652 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4351651 B x' t h1). Qed.
Lemma lem4351655 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351652 B x' t h1 (@lem4351642 A B s x t x' h2)). Qed.
Lemma lem4351656 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351655 A B s x t x' h1 h2). Qed.
Lemma lem4351658 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351659 : term764 = False.
Proof. exact (@lem4351658 False). Qed.
Lemma lem4351660 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351659) (@lem4351656 A B s x t x' h1 h2)). Qed.
Lemma lem4351662 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344110 A B s' x t' x' h1)). Qed.
Lemma lem4351663 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351662 A B s' x t' x' h1). Qed.
Lemma lem4351665 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351666 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351665 (t' x')). Qed.
Lemma lem4351667 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351666 B t' x') (@lem4351663 A B s' x t' x' h1)). Qed.
Lemma lem4351670 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351672 {B : Type'} (t' : B -> Prop) (_49628 : B) : (term99 B t' _49628) = (term98 B t' _49628).
Proof. exact (@lem4351670 (t' _49628)). Qed.
Lemma lem4351675 {B : Type'} (_49628 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49628.
Proof. exact (EQ_MP (@lem4351672 B t' _49628) (@lem4349468 B _49628 t' h1)). Qed.
Lemma lem4351676 {B : Type'} (_49628 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49628.
Proof. exact (@lem4351675 B _49628 t' h1). Qed.
Lemma lem4351677 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351676 B x' t' h1). Qed.
Lemma lem4351680 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351677 B x' t' h1 (@lem4351667 A B s' x t' x' h2)). Qed.
Lemma lem4351681 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351680 A B s' x t' x' h1 h2). Qed.
Lemma lem4351683 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351684 : term764 = False.
Proof. exact (@lem4351683 False). Qed.
Lemma lem4351685 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351684) (@lem4351681 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351687 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344119 A B s x t x' h1)). Qed.
Lemma lem4351688 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4351687 A B s x t x' h1). Qed.
Lemma lem4351690 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351691 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4351690 (t x')). Qed.
Lemma lem4351692 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4351691 B t x') (@lem4351688 A B s x t x' h1)). Qed.
Lemma lem4351695 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351697 {B : Type'} (t : B -> Prop) (_49631 : B) : (term99 B t _49631) = (term98 B t _49631).
Proof. exact (@lem4351695 (t _49631)). Qed.
Lemma lem4351700 {B : Type'} (_49631 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49631.
Proof. exact (EQ_MP (@lem4351697 B t _49631) (@lem4349482 B _49631 t h1)). Qed.
Lemma lem4351701 {B : Type'} (_49631 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49631.
Proof. exact (@lem4351700 B _49631 t h1). Qed.
Lemma lem4351702 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4351701 B x' t h1). Qed.
Lemma lem4351705 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351702 B x' t h1 (@lem4351692 A B s x t x' h2)). Qed.
Lemma lem4351706 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351705 A B s x t x' h1 h2). Qed.
Lemma lem4351708 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351709 : term764 = False.
Proof. exact (@lem4351708 False). Qed.
Lemma lem4351710 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351709) (@lem4351706 A B s x t x' h1 h2)). Qed.
Lemma lem4351712 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344115 B t t' x''' h1)). Qed.
Lemma lem4351713 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4351712 B t t' x''' h1). Qed.
Lemma lem4351715 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351716 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4351715 (t x''')). Qed.
Lemma lem4351717 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4351716 B t x''') (@lem4351713 B t t' x''' h1)). Qed.
Lemma lem4351720 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351722 {B : Type'} (t : B -> Prop) (_49633 : B) : (term99 B t _49633) = (term98 B t _49633).
Proof. exact (@lem4351720 (t _49633)). Qed.
Lemma lem4351725 {B : Type'} (_49633 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49633.
Proof. exact (EQ_MP (@lem4351722 B t _49633) (@lem4349494 B _49633 t h1)). Qed.
Lemma lem4351726 {B : Type'} (_49633 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49633.
Proof. exact (@lem4351725 B _49633 t h1). Qed.
Lemma lem4351727 {B : Type'} (x''' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'''.
Proof. exact (@lem4351726 B x''' t h1). Qed.
Lemma lem4351730 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4351727 B x''' t h1 (@lem4351717 B t t' x''' h2)). Qed.
Lemma lem4351731 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4351730 B t t' x''' h1 h2). Qed.
Lemma lem4351733 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351734 : term764 = False.
Proof. exact (@lem4351733 False). Qed.
Lemma lem4351735 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4351734) (@lem4351731 B t t' x''' h1 h2)). Qed.
Lemma lem4351737 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344127 A B s x t x' h1)). Qed.
Lemma lem4351738 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4351737 A B s x t x' h1). Qed.
Lemma lem4351740 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351741 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4351740 (t x')). Qed.
Lemma lem4351742 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4351741 B t x') (@lem4351738 A B s x t x' h1)). Qed.
Lemma lem4351745 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351747 {B : Type'} (t : B -> Prop) (_49635 : B) : (term99 B t _49635) = (term98 B t _49635).
Proof. exact (@lem4351745 (t _49635)). Qed.
Lemma lem4351750 {B : Type'} (_49635 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49635.
Proof. exact (EQ_MP (@lem4351747 B t _49635) (@lem4349506 B _49635 t h1)). Qed.
Lemma lem4351751 {B : Type'} (_49635 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49635.
Proof. exact (@lem4351750 B _49635 t h1). Qed.
Lemma lem4351752 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4351751 B x' t h1). Qed.
Lemma lem4351755 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4351752 B x' t h1 (@lem4351742 A B s x t x' h2)). Qed.
Lemma lem4351756 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351755 A B s x t x' h1 h2). Qed.
Lemma lem4351758 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351759 : term764 = False.
Proof. exact (@lem4351758 False). Qed.
Lemma lem4351760 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351759) (@lem4351756 A B s x t x' h1 h2)). Qed.
Lemma lem4351762 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344128 A B s' x t' x' h1)). Qed.
Lemma lem4351763 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351762 A B s' x t' x' h1). Qed.
Lemma lem4351765 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351766 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351765 (t' x')). Qed.
Lemma lem4351767 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351766 B t' x') (@lem4351763 A B s' x t' x' h1)). Qed.
Lemma lem4351770 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351772 {B : Type'} (t' : B -> Prop) (_49636 : B) : (term99 B t' _49636) = (term98 B t' _49636).
Proof. exact (@lem4351770 (t' _49636)). Qed.
Lemma lem4351775 {B : Type'} (_49636 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49636.
Proof. exact (EQ_MP (@lem4351772 B t' _49636) (@lem4349516 B _49636 t' h1)). Qed.
Lemma lem4351776 {B : Type'} (_49636 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49636.
Proof. exact (@lem4351775 B _49636 t' h1). Qed.
Lemma lem4351777 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351776 B x' t' h1). Qed.
Lemma lem4351780 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351777 B x' t' h1 (@lem4351767 A B s' x t' x' h2)). Qed.
Lemma lem4351781 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351780 A B s' x t' x' h1 h2). Qed.
Lemma lem4351783 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351784 : term764 = False.
Proof. exact (@lem4351783 False). Qed.
Lemma lem4351785 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351784) (@lem4351781 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351787 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344137 A s s' x'' h1)). Qed.
Lemma lem4351788 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4351787 A s s' x'' h1). Qed.
Lemma lem4351790 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351791 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4351790 (s x'')). Qed.
Lemma lem4351792 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4351791 A s x'') (@lem4351788 A s s' x'' h1)). Qed.
Lemma lem4351798 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4351799 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : (term163 A s s' _49639) = (term765 A s' s _49639).
Proof. exact (@lem4351798 (s' _49639) (term99 A s _49639)). Qed.
Lemma lem4351805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4351806 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : (term766 A s s' _49639) = (term767 A s' s _49639).
Proof. exact (MK_COMB (@lem4351805) (@lem4351799 A s' s _49639)). Qed.
Lemma lem4351812 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : (term765 A s' s _49639) = (term765 A s' s _49639).
Proof. exact (eq_refl (term765 A s' s _49639)). Qed.
Lemma lem4351813 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : ((term163 A s s' _49639) = (term765 A s' s _49639)) = ((term765 A s' s _49639) = (term765 A s' s _49639)).
Proof. exact (MK_COMB (@lem4351806 A s' s _49639) (@lem4351812 A s' s _49639)). Qed.
Lemma lem4351815 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4351816 (x : Prop) : (x = x) = True.
Proof. exact (@lem4351815 Prop x). Qed.
Lemma lem4351817 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : ((term765 A s' s _49639) = (term765 A s' s _49639)) = True.
Proof. exact (@lem4351816 (term765 A s' s _49639)). Qed.
Lemma lem4351818 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : ((term163 A s s' _49639) = (term765 A s' s _49639)) = True.
Proof. exact (TRANS (@lem4351813 A s' s _49639) (@lem4351817 A s' s _49639)). Qed.
Lemma lem4351819 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : True = ((term163 A s s' _49639) = (term765 A s' s _49639)).
Proof. exact (SYM (@lem4351818 A s' s _49639)). Qed.
Lemma lem4351820 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49639 : A) : (term163 A s s' _49639) = (term765 A s' s _49639).
Proof. exact (EQ_MP (@lem4351819 A s' s _49639) (@lem0)). Qed.
Lemma lem4351821 {A B : Type'} (_49639 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 A s' s _49639.
Proof. exact (EQ_MP (@lem4351820 A s' s _49639) (@lem4349534 A B _49639 s s' t t' h1)). Qed.
Lemma lem4351823 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4351824 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49639 : A) : (term765 A s' s _49639) = (term769 A s s' _49639).
Proof. exact (@lem4351823 (term99 A s _49639) (s' _49639)). Qed.
Lemma lem4351826 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4351827 {A : Type'} (s : A -> Prop) (_49639 : A) : (term151 A s _49639) = (s _49639).
Proof. exact (@lem4351826 (s _49639)). Qed.
Lemma lem4351828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4351829 {A : Type'} (s : A -> Prop) (_49639 : A) : (term770 A s _49639) = (term96 A s _49639).
Proof. exact (MK_COMB (@lem4351828) (@lem4351827 A s _49639)). Qed.
Lemma lem4351830 {A : Type'} (s' : A -> Prop) (_49639 : A) : (s' _49639) = (s' _49639).
Proof. exact (eq_refl (s' _49639)). Qed.
Lemma lem4351831 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49639 : A) : (term769 A s s' _49639) = (term114 A s s' _49639).
Proof. exact (MK_COMB (@lem4351829 A s _49639) (@lem4351830 A s' _49639)). Qed.
Lemma lem4351832 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49639 : A) : (term765 A s' s _49639) = (term114 A s s' _49639).
Proof. exact (TRANS (@lem4351824 A s s' _49639) (@lem4351831 A s s' _49639)). Qed.
Lemma lem4351835 {A B : Type'} (_49639 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49639.
Proof. exact (EQ_MP (@lem4351832 A s s' _49639) (@lem4351821 A B _49639 s s' t t' h1)). Qed.
Lemma lem4351836 {A B : Type'} (_49639 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49639.
Proof. exact (@lem4351835 A B _49639 s s' t t' h1). Qed.
Lemma lem4351837 {A B : Type'} (x'' : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' x''.
Proof. exact (@lem4351836 A B x'' s s' t t' h1). Qed.
Lemma lem4351840 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (@lem4351837 A B x'' s s' t t' h1 (@lem4351792 A s s' x'' h2)). Qed.
Lemma lem4351841 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4351840 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4351843 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351844 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4351843 (s' x'')). Qed.
Lemma lem4351845 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (EQ_MP (@lem4351844 A s' x'') (@lem4351841 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4351848 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351850 {A : Type'} (s' : A -> Prop) (x'' : A) : (term99 A s' x'') = (term98 A s' x'').
Proof. exact (@lem4351848 (s' x'')). Qed.
Lemma lem4351853 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term98 A s' x''.
Proof. exact (EQ_MP (@lem4351850 A s' x'') (@lem4349544 A s s' x'' h1)). Qed.
Lemma lem4351856 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4351853 A s s' x'' h2 (@lem4351845 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4351857 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4351856 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4351859 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351860 : term764 = False.
Proof. exact (@lem4351859 False). Qed.
Lemma lem4351861 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4351860) (@lem4351857 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4351863 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344142 A B s' x t' x' h1)). Qed.
Lemma lem4351864 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351863 A B s' x t' x' h1). Qed.
Lemma lem4351866 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351867 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351866 (t' x')). Qed.
Lemma lem4351868 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351867 B t' x') (@lem4351864 A B s' x t' x' h1)). Qed.
Lemma lem4351871 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351873 {B : Type'} (t' : B -> Prop) (_49641 : B) : (term99 B t' _49641) = (term98 B t' _49641).
Proof. exact (@lem4351871 (t' _49641)). Qed.
Lemma lem4351876 {B : Type'} (_49641 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49641.
Proof. exact (EQ_MP (@lem4351873 B t' _49641) (@lem4349550 B _49641 t' h1)). Qed.
Lemma lem4351877 {B : Type'} (_49641 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49641.
Proof. exact (@lem4351876 B _49641 t' h1). Qed.
Lemma lem4351878 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351877 B x' t' h1). Qed.
Lemma lem4351881 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351878 B x' t' h1 (@lem4351868 A B s' x t' x' h2)). Qed.
Lemma lem4351882 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351881 A B s' x t' x' h1 h2). Qed.
Lemma lem4351884 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351885 : term764 = False.
Proof. exact (@lem4351884 False). Qed.
Lemma lem4351886 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351885) (@lem4351882 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351888 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344149 A B s x t x' h1)). Qed.
Lemma lem4351889 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4351888 A B s x t x' h1). Qed.
Lemma lem4351891 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351892 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4351891 (t x')). Qed.
Lemma lem4351893 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4351892 B t x') (@lem4351889 A B s x t x' h1)). Qed.
Lemma lem4351899 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4351900 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : (term163 B t t' _49646) = (term765 B t' t _49646).
Proof. exact (@lem4351899 (t' _49646) (term99 B t _49646)). Qed.
Lemma lem4351906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4351907 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : (term766 B t t' _49646) = (term767 B t' t _49646).
Proof. exact (MK_COMB (@lem4351906) (@lem4351900 B t' t _49646)). Qed.
Lemma lem4351913 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : (term765 B t' t _49646) = (term765 B t' t _49646).
Proof. exact (eq_refl (term765 B t' t _49646)). Qed.
Lemma lem4351914 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : ((term163 B t t' _49646) = (term765 B t' t _49646)) = ((term765 B t' t _49646) = (term765 B t' t _49646)).
Proof. exact (MK_COMB (@lem4351907 B t' t _49646) (@lem4351913 B t' t _49646)). Qed.
Lemma lem4351916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4351917 (x : Prop) : (x = x) = True.
Proof. exact (@lem4351916 Prop x). Qed.
Lemma lem4351918 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : ((term765 B t' t _49646) = (term765 B t' t _49646)) = True.
Proof. exact (@lem4351917 (term765 B t' t _49646)). Qed.
Lemma lem4351919 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : ((term163 B t t' _49646) = (term765 B t' t _49646)) = True.
Proof. exact (TRANS (@lem4351914 B t' t _49646) (@lem4351918 B t' t _49646)). Qed.
Lemma lem4351920 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : True = ((term163 B t t' _49646) = (term765 B t' t _49646)).
Proof. exact (SYM (@lem4351919 B t' t _49646)). Qed.
Lemma lem4351921 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49646 : B) : (term163 B t t' _49646) = (term765 B t' t _49646).
Proof. exact (EQ_MP (@lem4351920 B t' t _49646) (@lem0)). Qed.
Lemma lem4351922 {A B : Type'} (_49646 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 B t' t _49646.
Proof. exact (EQ_MP (@lem4351921 B t' t _49646) (@lem4349584 A B _49646 s s' t t' h1)). Qed.
Lemma lem4351924 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4351925 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49646 : B) : (term765 B t' t _49646) = (term769 B t t' _49646).
Proof. exact (@lem4351924 (term99 B t _49646) (t' _49646)). Qed.
Lemma lem4351927 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4351928 {B : Type'} (t : B -> Prop) (_49646 : B) : (term151 B t _49646) = (t _49646).
Proof. exact (@lem4351927 (t _49646)). Qed.
Lemma lem4351929 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4351930 {B : Type'} (t : B -> Prop) (_49646 : B) : (term770 B t _49646) = (term96 B t _49646).
Proof. exact (MK_COMB (@lem4351929) (@lem4351928 B t _49646)). Qed.
Lemma lem4351931 {B : Type'} (t' : B -> Prop) (_49646 : B) : (t' _49646) = (t' _49646).
Proof. exact (eq_refl (t' _49646)). Qed.
Lemma lem4351932 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49646 : B) : (term769 B t t' _49646) = (term114 B t t' _49646).
Proof. exact (MK_COMB (@lem4351930 B t _49646) (@lem4351931 B t' _49646)). Qed.
Lemma lem4351933 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49646 : B) : (term765 B t' t _49646) = (term114 B t t' _49646).
Proof. exact (TRANS (@lem4351925 B t t' _49646) (@lem4351932 B t t' _49646)). Qed.
Lemma lem4351936 {A B : Type'} (_49646 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49646.
Proof. exact (EQ_MP (@lem4351933 B t t' _49646) (@lem4351922 A B _49646 s s' t t' h1)). Qed.
Lemma lem4351937 {A B : Type'} (_49646 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49646.
Proof. exact (@lem4351936 A B _49646 s s' t t' h1). Qed.
Lemma lem4351938 {A B : Type'} (x' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' x'.
Proof. exact (@lem4351937 A B x' s s' t t' h1). Qed.
Lemma lem4351941 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term179 A B s s' t t') (h2 : term267 A B s x t x') : t' x'.
Proof. exact (@lem4351938 A B x' s s' t t' h1 (@lem4351893 A B s x t x' h2)). Qed.
Lemma lem4351942 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term179 A B s s' t t') (h2 : term267 A B s x t x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351941 A B s' t' s x t x' h1 h2). Qed.
Lemma lem4351944 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351945 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351944 (t' x')). Qed.
Lemma lem4351946 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term179 A B s s' t t') (h2 : term267 A B s x t x') : t' x'.
Proof. exact (EQ_MP (@lem4351945 B t' x') (@lem4351942 A B s' t' s x t x' h1 h2)). Qed.
Lemma lem4351949 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351951 {B : Type'} (t' : B -> Prop) (_49644 : B) : (term99 B t' _49644) = (term98 B t' _49644).
Proof. exact (@lem4351949 (t' _49644)). Qed.
Lemma lem4351954 {B : Type'} (_49644 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49644.
Proof. exact (EQ_MP (@lem4351951 B t' _49644) (@lem4349572 B _49644 t' h1)). Qed.
Lemma lem4351955 {B : Type'} (_49644 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49644.
Proof. exact (@lem4351954 B _49644 t' h1). Qed.
Lemma lem4351956 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351955 B x' t' h1). Qed.
Lemma lem4351959 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : False.
Proof. exact (@lem4351956 B x' t' h1 (@lem4351946 A B s' t' s x t x' h2 h3)). Qed.
Lemma lem4351960 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351959 A B s' t' s x t x' h1 h2 h3). Qed.
Lemma lem4351962 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351963 : term764 = False.
Proof. exact (@lem4351962 False). Qed.
Lemma lem4351964 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4351963) (@lem4351960 A B s' t' s x t x' h1 h2 h3)). Qed.
Lemma lem4351966 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344150 A B s' x t' x' h1)). Qed.
Lemma lem4351967 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4351966 A B s' x t' x' h1). Qed.
Lemma lem4351969 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351970 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4351969 (t' x')). Qed.
Lemma lem4351971 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4351970 B t' x') (@lem4351967 A B s' x t' x' h1)). Qed.
Lemma lem4351974 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4351976 {B : Type'} (t' : B -> Prop) (_49647 : B) : (term99 B t' _49647) = (term98 B t' _49647).
Proof. exact (@lem4351974 (t' _49647)). Qed.
Lemma lem4351979 {B : Type'} (_49647 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49647.
Proof. exact (EQ_MP (@lem4351976 B t' _49647) (@lem4349594 B _49647 t' h1)). Qed.
Lemma lem4351980 {B : Type'} (_49647 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49647.
Proof. exact (@lem4351979 B _49647 t' h1). Qed.
Lemma lem4351981 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4351980 B x' t' h1). Qed.
Lemma lem4351984 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4351981 B x' t' h1 (@lem4351971 A B s' x t' x' h2)). Qed.
Lemma lem4351985 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4351984 A B s' x t' x' h1 h2). Qed.
Lemma lem4351987 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351988 : term764 = False.
Proof. exact (@lem4351987 False). Qed.
Lemma lem4351989 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4351988) (@lem4351985 A B s' x t' x' h1 h2)). Qed.
Lemma lem4351991 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344155 B t t' x''' h1)). Qed.
Lemma lem4351992 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4351991 B t t' x''' h1). Qed.
Lemma lem4351994 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4351995 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4351994 (t x''')). Qed.
Lemma lem4351996 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4351995 B t x''') (@lem4351992 B t t' x''' h1)). Qed.
Lemma lem4352002 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352003 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : (term163 B t t' _49652) = (term765 B t' t _49652).
Proof. exact (@lem4352002 (t' _49652) (term99 B t _49652)). Qed.
Lemma lem4352009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352010 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : (term766 B t t' _49652) = (term767 B t' t _49652).
Proof. exact (MK_COMB (@lem4352009) (@lem4352003 B t' t _49652)). Qed.
Lemma lem4352016 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : (term765 B t' t _49652) = (term765 B t' t _49652).
Proof. exact (eq_refl (term765 B t' t _49652)). Qed.
Lemma lem4352017 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : ((term163 B t t' _49652) = (term765 B t' t _49652)) = ((term765 B t' t _49652) = (term765 B t' t _49652)).
Proof. exact (MK_COMB (@lem4352010 B t' t _49652) (@lem4352016 B t' t _49652)). Qed.
Lemma lem4352019 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352020 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352019 Prop x). Qed.
Lemma lem4352021 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : ((term765 B t' t _49652) = (term765 B t' t _49652)) = True.
Proof. exact (@lem4352020 (term765 B t' t _49652)). Qed.
Lemma lem4352022 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : ((term163 B t t' _49652) = (term765 B t' t _49652)) = True.
Proof. exact (TRANS (@lem4352017 B t' t _49652) (@lem4352021 B t' t _49652)). Qed.
Lemma lem4352023 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : True = ((term163 B t t' _49652) = (term765 B t' t _49652)).
Proof. exact (SYM (@lem4352022 B t' t _49652)). Qed.
Lemma lem4352024 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49652 : B) : (term163 B t t' _49652) = (term765 B t' t _49652).
Proof. exact (EQ_MP (@lem4352023 B t' t _49652) (@lem0)). Qed.
Lemma lem4352025 {A B : Type'} (_49652 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 B t' t _49652.
Proof. exact (EQ_MP (@lem4352024 B t' t _49652) (@lem4349628 A B _49652 s s' t t' h1)). Qed.
Lemma lem4352027 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352028 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49652 : B) : (term765 B t' t _49652) = (term769 B t t' _49652).
Proof. exact (@lem4352027 (term99 B t _49652) (t' _49652)). Qed.
Lemma lem4352030 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352031 {B : Type'} (t : B -> Prop) (_49652 : B) : (term151 B t _49652) = (t _49652).
Proof. exact (@lem4352030 (t _49652)). Qed.
Lemma lem4352032 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352033 {B : Type'} (t : B -> Prop) (_49652 : B) : (term770 B t _49652) = (term96 B t _49652).
Proof. exact (MK_COMB (@lem4352032) (@lem4352031 B t _49652)). Qed.
Lemma lem4352034 {B : Type'} (t' : B -> Prop) (_49652 : B) : (t' _49652) = (t' _49652).
Proof. exact (eq_refl (t' _49652)). Qed.
Lemma lem4352035 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49652 : B) : (term769 B t t' _49652) = (term114 B t t' _49652).
Proof. exact (MK_COMB (@lem4352033 B t _49652) (@lem4352034 B t' _49652)). Qed.
Lemma lem4352036 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49652 : B) : (term765 B t' t _49652) = (term114 B t t' _49652).
Proof. exact (TRANS (@lem4352028 B t t' _49652) (@lem4352035 B t t' _49652)). Qed.
Lemma lem4352039 {A B : Type'} (_49652 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49652.
Proof. exact (EQ_MP (@lem4352036 B t t' _49652) (@lem4352025 A B _49652 s s' t t' h1)). Qed.
Lemma lem4352040 {A B : Type'} (_49652 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49652.
Proof. exact (@lem4352039 A B _49652 s s' t t' h1). Qed.
Lemma lem4352041 {A B : Type'} (x''' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' x'''.
Proof. exact (@lem4352040 A B x''' s s' t t' h1). Qed.
Lemma lem4352044 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (@lem4352041 A B x''' s s' t t' h1 (@lem4351996 B t t' x''' h2)). Qed.
Lemma lem4352045 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4352044 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4352047 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352048 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4352047 (t' x''')). Qed.
Lemma lem4352049 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (EQ_MP (@lem4352048 B t' x''') (@lem4352045 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4352052 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352054 {B : Type'} (t' : B -> Prop) (x''' : B) : (term99 B t' x''') = (term98 B t' x''').
Proof. exact (@lem4352052 (t' x''')). Qed.
Lemma lem4352057 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term98 B t' x'''.
Proof. exact (EQ_MP (@lem4352054 B t' x''') (@lem4349632 B t t' x''' h1)). Qed.
Lemma lem4352060 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4352057 B t t' x''' h2 (@lem4352049 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4352061 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4352060 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4352063 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352064 : term764 = False.
Proof. exact (@lem4352063 False). Qed.
Lemma lem4352065 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4352064) (@lem4352061 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4352067 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344160 A B s' x t' x' h1)). Qed.
Lemma lem4352068 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4352067 A B s' x t' x' h1). Qed.
Lemma lem4352070 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352071 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4352070 (t' x')). Qed.
Lemma lem4352072 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4352071 B t' x') (@lem4352068 A B s' x t' x' h1)). Qed.
Lemma lem4352075 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352077 {B : Type'} (t' : B -> Prop) (_49653 : B) : (term99 B t' _49653) = (term98 B t' _49653).
Proof. exact (@lem4352075 (t' _49653)). Qed.
Lemma lem4352080 {B : Type'} (_49653 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49653.
Proof. exact (EQ_MP (@lem4352077 B t' _49653) (@lem4349638 B _49653 t' h1)). Qed.
Lemma lem4352081 {B : Type'} (_49653 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49653.
Proof. exact (@lem4352080 B _49653 t' h1). Qed.
Lemma lem4352082 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4352081 B x' t' h1). Qed.
Lemma lem4352085 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4352082 B x' t' h1 (@lem4352072 A B s' x t' x' h2)). Qed.
Lemma lem4352086 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352085 A B s' x t' x' h1 h2). Qed.
Lemma lem4352088 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352089 : term764 = False.
Proof. exact (@lem4352088 False). Qed.
Lemma lem4352090 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4352089) (@lem4352086 A B s' x t' x' h1 h2)). Qed.
Lemma lem4352092 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344156 B t' t x''' h1)). Qed.
Lemma lem4352093 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4352092 B t' t x''' h1). Qed.
Lemma lem4352095 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352096 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4352095 (t' x''')). Qed.
Lemma lem4352097 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4352096 B t' x''') (@lem4352093 B t' t x''' h1)). Qed.
Lemma lem4352100 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352102 {B : Type'} (t' : B -> Prop) (_49656 : B) : (term99 B t' _49656) = (term98 B t' _49656).
Proof. exact (@lem4352100 (t' _49656)). Qed.
Lemma lem4352105 {B : Type'} (_49656 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49656.
Proof. exact (EQ_MP (@lem4352102 B t' _49656) (@lem4349660 B _49656 t' h1)). Qed.
Lemma lem4352106 {B : Type'} (_49656 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49656.
Proof. exact (@lem4352105 B _49656 t' h1). Qed.
Lemma lem4352107 {B : Type'} (x''' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'''.
Proof. exact (@lem4352106 B x''' t' h1). Qed.
Lemma lem4352110 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (@lem4352107 B x''' t' h1 (@lem4352097 B t' t x''' h2)). Qed.
Lemma lem4352111 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4352110 B t' t x''' h1 h2). Qed.
Lemma lem4352113 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352114 : term764 = False.
Proof. exact (@lem4352113 False). Qed.
Lemma lem4352115 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4352114) (@lem4352111 B t' t x''' h1 h2)). Qed.
Lemma lem4352117 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344168 A B s' x t' x' h1)). Qed.
Lemma lem4352118 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4352117 A B s' x t' x' h1). Qed.
Lemma lem4352120 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352121 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4352120 (t' x')). Qed.
Lemma lem4352122 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4352121 B t' x') (@lem4352118 A B s' x t' x' h1)). Qed.
Lemma lem4352125 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352127 {B : Type'} (t' : B -> Prop) (_49659 : B) : (term99 B t' _49659) = (term98 B t' _49659).
Proof. exact (@lem4352125 (t' _49659)). Qed.
Lemma lem4352130 {B : Type'} (_49659 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49659.
Proof. exact (EQ_MP (@lem4352127 B t' _49659) (@lem4349682 B _49659 t' h1)). Qed.
Lemma lem4352131 {B : Type'} (_49659 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49659.
Proof. exact (@lem4352130 B _49659 t' h1). Qed.
Lemma lem4352132 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4352131 B x' t' h1). Qed.
Lemma lem4352135 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (@lem4352132 B x' t' h1 (@lem4352122 A B s' x t' x' h2)). Qed.
Lemma lem4352136 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352135 A B s' x t' x' h1 h2). Qed.
Lemma lem4352138 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352139 : term764 = False.
Proof. exact (@lem4352138 False). Qed.
Lemma lem4352140 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4352139) (@lem4352136 A B s' x t' x' h1 h2)). Qed.
Lemma lem4352142 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344183 A B s x t x' h1)). Qed.
Lemma lem4352143 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4352142 A B s x t x' h1). Qed.
Lemma lem4352145 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352146 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4352145 (s x)). Qed.
Lemma lem4352147 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4352146 A s x) (@lem4352143 A B s x t x' h1)). Qed.
Lemma lem4352150 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352152 {A : Type'} (s : A -> Prop) (_49664 : A) : (term99 A s _49664) = (term98 A s _49664).
Proof. exact (@lem4352150 (s _49664)). Qed.
Lemma lem4352155 {A : Type'} (_49664 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49664.
Proof. exact (EQ_MP (@lem4352152 A s _49664) (@lem4349716 A _49664 s h1)). Qed.
Lemma lem4352156 {A : Type'} (_49664 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49664.
Proof. exact (@lem4352155 A _49664 s h1). Qed.
Lemma lem4352157 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4352156 A x s h1). Qed.
Lemma lem4352160 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352157 A x s h1 (@lem4352147 A B s x t x' h2)). Qed.
Lemma lem4352161 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352160 A B s x t x' h1 h2). Qed.
Lemma lem4352163 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352164 : term764 = False.
Proof. exact (@lem4352163 False). Qed.
Lemma lem4352165 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352164) (@lem4352161 A B s x t x' h1 h2)). Qed.
Lemma lem4352167 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344179 A s s' x'' h1)). Qed.
Lemma lem4352168 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4352167 A s s' x'' h1). Qed.
Lemma lem4352170 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352171 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4352170 (s x'')). Qed.
Lemma lem4352172 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4352171 A s x'') (@lem4352168 A s s' x'' h1)). Qed.
Lemma lem4352175 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352177 {A : Type'} (s : A -> Prop) (_49667 : A) : (term99 A s _49667) = (term98 A s _49667).
Proof. exact (@lem4352175 (s _49667)). Qed.
Lemma lem4352180 {A : Type'} (_49667 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49667.
Proof. exact (EQ_MP (@lem4352177 A s _49667) (@lem4349738 A _49667 s h1)). Qed.
Lemma lem4352181 {A : Type'} (_49667 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49667.
Proof. exact (@lem4352180 A _49667 s h1). Qed.
Lemma lem4352182 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x''.
Proof. exact (@lem4352181 A x'' s h1). Qed.
Lemma lem4352185 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4352182 A x'' s h1 (@lem4352172 A s s' x'' h2)). Qed.
Lemma lem4352186 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4352185 A s s' x'' h1 h2). Qed.
Lemma lem4352188 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352189 : term764 = False.
Proof. exact (@lem4352188 False). Qed.
Lemma lem4352190 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4352189) (@lem4352186 A s s' x'' h1 h2)). Qed.
Lemma lem4352192 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344191 A B s x t x' h1)). Qed.
Lemma lem4352193 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4352192 A B s x t x' h1). Qed.
Lemma lem4352195 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352196 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4352195 (s x)). Qed.
Lemma lem4352197 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4352196 A s x) (@lem4352193 A B s x t x' h1)). Qed.
Lemma lem4352200 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352202 {A : Type'} (s : A -> Prop) (_49670 : A) : (term99 A s _49670) = (term98 A s _49670).
Proof. exact (@lem4352200 (s _49670)). Qed.
Lemma lem4352205 {A : Type'} (_49670 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49670.
Proof. exact (EQ_MP (@lem4352202 A s _49670) (@lem4349760 A _49670 s h1)). Qed.
Lemma lem4352206 {A : Type'} (_49670 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49670.
Proof. exact (@lem4352205 A _49670 s h1). Qed.
Lemma lem4352207 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4352206 A x s h1). Qed.
Lemma lem4352210 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352207 A x s h1 (@lem4352197 A B s x t x' h2)). Qed.
Lemma lem4352211 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352210 A B s x t x' h1 h2). Qed.
Lemma lem4352213 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352214 : term764 = False.
Proof. exact (@lem4352213 False). Qed.
Lemma lem4352215 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352214) (@lem4352211 A B s x t x' h1 h2)). Qed.
Lemma lem4352217 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344180 A s' s x'' h1)). Qed.
Lemma lem4352218 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4352217 A s' s x'' h1). Qed.
Lemma lem4352220 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352221 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4352220 (s' x'')). Qed.
Lemma lem4352222 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4352221 A s' x'') (@lem4352218 A s' s x'' h1)). Qed.
Lemma lem4352228 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352229 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : (term163 A s' s _49671) = (term765 A s s' _49671).
Proof. exact (@lem4352228 (s _49671) (term99 A s' _49671)). Qed.
Lemma lem4352235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352236 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : (term766 A s' s _49671) = (term767 A s s' _49671).
Proof. exact (MK_COMB (@lem4352235) (@lem4352229 A s s' _49671)). Qed.
Lemma lem4352242 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : (term765 A s s' _49671) = (term765 A s s' _49671).
Proof. exact (eq_refl (term765 A s s' _49671)). Qed.
Lemma lem4352243 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : ((term163 A s' s _49671) = (term765 A s s' _49671)) = ((term765 A s s' _49671) = (term765 A s s' _49671)).
Proof. exact (MK_COMB (@lem4352236 A s s' _49671) (@lem4352242 A s s' _49671)). Qed.
Lemma lem4352245 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352246 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352245 Prop x). Qed.
Lemma lem4352247 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : ((term765 A s s' _49671) = (term765 A s s' _49671)) = True.
Proof. exact (@lem4352246 (term765 A s s' _49671)). Qed.
Lemma lem4352248 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : ((term163 A s' s _49671) = (term765 A s s' _49671)) = True.
Proof. exact (TRANS (@lem4352243 A s s' _49671) (@lem4352247 A s s' _49671)). Qed.
Lemma lem4352249 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : True = ((term163 A s' s _49671) = (term765 A s s' _49671)).
Proof. exact (SYM (@lem4352248 A s s' _49671)). Qed.
Lemma lem4352250 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49671 : A) : (term163 A s' s _49671) = (term765 A s s' _49671).
Proof. exact (EQ_MP (@lem4352249 A s s' _49671) (@lem0)). Qed.
Lemma lem4352251 {A B : Type'} (_49671 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 A s s' _49671.
Proof. exact (EQ_MP (@lem4352250 A s s' _49671) (@lem4349774 A B _49671 s' s t' t h1)). Qed.
Lemma lem4352253 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352254 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49671 : A) : (term765 A s s' _49671) = (term769 A s' s _49671).
Proof. exact (@lem4352253 (term99 A s' _49671) (s _49671)). Qed.
Lemma lem4352256 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352257 {A : Type'} (s' : A -> Prop) (_49671 : A) : (term151 A s' _49671) = (s' _49671).
Proof. exact (@lem4352256 (s' _49671)). Qed.
Lemma lem4352258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352259 {A : Type'} (s' : A -> Prop) (_49671 : A) : (term770 A s' _49671) = (term96 A s' _49671).
Proof. exact (MK_COMB (@lem4352258) (@lem4352257 A s' _49671)). Qed.
Lemma lem4352260 {A : Type'} (s : A -> Prop) (_49671 : A) : (s _49671) = (s _49671).
Proof. exact (eq_refl (s _49671)). Qed.
Lemma lem4352261 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49671 : A) : (term769 A s' s _49671) = (term114 A s' s _49671).
Proof. exact (MK_COMB (@lem4352259 A s' _49671) (@lem4352260 A s _49671)). Qed.
Lemma lem4352262 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49671 : A) : (term765 A s s' _49671) = (term114 A s' s _49671).
Proof. exact (TRANS (@lem4352254 A s' s _49671) (@lem4352261 A s' s _49671)). Qed.
Lemma lem4352265 {A B : Type'} (_49671 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49671.
Proof. exact (EQ_MP (@lem4352262 A s' s _49671) (@lem4352251 A B _49671 s' s t' t h1)). Qed.
Lemma lem4352266 {A B : Type'} (_49671 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49671.
Proof. exact (@lem4352265 A B _49671 s' s t' t h1). Qed.
Lemma lem4352267 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s x''.
Proof. exact (@lem4352266 A B x'' s' s t' t h1). Qed.
Lemma lem4352270 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (@lem4352267 A B x'' s' s t' t h1 (@lem4352222 A s' s x'' h2)). Qed.
Lemma lem4352271 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4352270 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4352273 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352274 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4352273 (s x'')). Qed.
Lemma lem4352275 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (EQ_MP (@lem4352274 A s x'') (@lem4352271 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4352278 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352280 {A : Type'} (s : A -> Prop) (x'' : A) : (term99 A s x'') = (term98 A s x'').
Proof. exact (@lem4352278 (s x'')). Qed.
Lemma lem4352283 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term98 A s x''.
Proof. exact (EQ_MP (@lem4352280 A s x'') (@lem4349786 A s' s x'' h1)). Qed.
Lemma lem4352286 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (@lem4352283 A s' s x'' h2 (@lem4352275 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4352287 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4352286 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4352289 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352290 : term764 = False.
Proof. exact (@lem4352289 False). Qed.
Lemma lem4352291 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4352290) (@lem4352287 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4352293 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344201 A B s x t x' h1)). Qed.
Lemma lem4352294 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4352293 A B s x t x' h1). Qed.
Lemma lem4352296 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352297 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4352296 (s x)). Qed.
Lemma lem4352298 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4352297 A s x) (@lem4352294 A B s x t x' h1)). Qed.
Lemma lem4352301 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352303 {A : Type'} (s : A -> Prop) (_49676 : A) : (term99 A s _49676) = (term98 A s _49676).
Proof. exact (@lem4352301 (s _49676)). Qed.
Lemma lem4352306 {A : Type'} (_49676 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49676.
Proof. exact (EQ_MP (@lem4352303 A s _49676) (@lem4349804 A _49676 s h1)). Qed.
Lemma lem4352307 {A : Type'} (_49676 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49676.
Proof. exact (@lem4352306 A _49676 s h1). Qed.
Lemma lem4352308 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4352307 A x s h1). Qed.
Lemma lem4352311 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352308 A x s h1 (@lem4352298 A B s x t x' h2)). Qed.
Lemma lem4352312 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352311 A B s x t x' h1 h2). Qed.
Lemma lem4352314 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352315 : term764 = False.
Proof. exact (@lem4352314 False). Qed.
Lemma lem4352316 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352315) (@lem4352312 A B s x t x' h1 h2)). Qed.
Lemma lem4352318 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (proj1 (@lem4344202 A B s' x t' x' h1)). Qed.
Lemma lem4352319 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4352318 A B s' x t' x' h1). Qed.
Lemma lem4352321 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352322 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4352321 (s' x)). Qed.
Lemma lem4352323 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : s' x.
Proof. exact (EQ_MP (@lem4352322 A s' x) (@lem4352319 A B s' x t' x' h1)). Qed.
Lemma lem4352329 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352330 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : (term163 A s' s _49677) = (term765 A s s' _49677).
Proof. exact (@lem4352329 (s _49677) (term99 A s' _49677)). Qed.
Lemma lem4352336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352337 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : (term766 A s' s _49677) = (term767 A s s' _49677).
Proof. exact (MK_COMB (@lem4352336) (@lem4352330 A s s' _49677)). Qed.
Lemma lem4352343 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : (term765 A s s' _49677) = (term765 A s s' _49677).
Proof. exact (eq_refl (term765 A s s' _49677)). Qed.
Lemma lem4352344 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : ((term163 A s' s _49677) = (term765 A s s' _49677)) = ((term765 A s s' _49677) = (term765 A s s' _49677)).
Proof. exact (MK_COMB (@lem4352337 A s s' _49677) (@lem4352343 A s s' _49677)). Qed.
Lemma lem4352346 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352347 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352346 Prop x). Qed.
Lemma lem4352348 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : ((term765 A s s' _49677) = (term765 A s s' _49677)) = True.
Proof. exact (@lem4352347 (term765 A s s' _49677)). Qed.
Lemma lem4352349 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : ((term163 A s' s _49677) = (term765 A s s' _49677)) = True.
Proof. exact (TRANS (@lem4352344 A s s' _49677) (@lem4352348 A s s' _49677)). Qed.
Lemma lem4352350 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : True = ((term163 A s' s _49677) = (term765 A s s' _49677)).
Proof. exact (SYM (@lem4352349 A s s' _49677)). Qed.
Lemma lem4352351 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49677 : A) : (term163 A s' s _49677) = (term765 A s s' _49677).
Proof. exact (EQ_MP (@lem4352350 A s s' _49677) (@lem0)). Qed.
Lemma lem4352352 {A B : Type'} (_49677 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 A s s' _49677.
Proof. exact (EQ_MP (@lem4352351 A s s' _49677) (@lem4349818 A B _49677 s' s t' t h1)). Qed.
Lemma lem4352354 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352355 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49677 : A) : (term765 A s s' _49677) = (term769 A s' s _49677).
Proof. exact (@lem4352354 (term99 A s' _49677) (s _49677)). Qed.
Lemma lem4352357 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352358 {A : Type'} (s' : A -> Prop) (_49677 : A) : (term151 A s' _49677) = (s' _49677).
Proof. exact (@lem4352357 (s' _49677)). Qed.
Lemma lem4352359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352360 {A : Type'} (s' : A -> Prop) (_49677 : A) : (term770 A s' _49677) = (term96 A s' _49677).
Proof. exact (MK_COMB (@lem4352359) (@lem4352358 A s' _49677)). Qed.
Lemma lem4352361 {A : Type'} (s : A -> Prop) (_49677 : A) : (s _49677) = (s _49677).
Proof. exact (eq_refl (s _49677)). Qed.
Lemma lem4352362 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49677 : A) : (term769 A s' s _49677) = (term114 A s' s _49677).
Proof. exact (MK_COMB (@lem4352360 A s' _49677) (@lem4352361 A s _49677)). Qed.
Lemma lem4352363 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49677 : A) : (term765 A s s' _49677) = (term114 A s' s _49677).
Proof. exact (TRANS (@lem4352355 A s' s _49677) (@lem4352362 A s' s _49677)). Qed.
Lemma lem4352366 {A B : Type'} (_49677 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49677.
Proof. exact (EQ_MP (@lem4352363 A s' s _49677) (@lem4352352 A B _49677 s' s t' t h1)). Qed.
Lemma lem4352367 {A B : Type'} (_49677 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49677.
Proof. exact (@lem4352366 A B _49677 s' s t' t h1). Qed.
Lemma lem4352368 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s x.
Proof. exact (@lem4352367 A B x s' s t' t h1). Qed.
Lemma lem4352371 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term179 A B s' s t' t) (h2 : term267 A B s' x t' x') : s x.
Proof. exact (@lem4352368 A B x s' s t' t h1 (@lem4352323 A B s' x t' x' h2)). Qed.
Lemma lem4352372 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term179 A B s' s t' t) (h2 : term267 A B s' x t' x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4352371 A B s t s' x t' x' h1 h2). Qed.
Lemma lem4352374 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352375 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4352374 (s x)). Qed.
Lemma lem4352376 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term179 A B s' s t' t) (h2 : term267 A B s' x t' x') : s x.
Proof. exact (EQ_MP (@lem4352375 A s x) (@lem4352372 A B s t s' x t' x' h1 h2)). Qed.
Lemma lem4352379 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352381 {A : Type'} (s : A -> Prop) (_49679 : A) : (term99 A s _49679) = (term98 A s _49679).
Proof. exact (@lem4352379 (s _49679)). Qed.
Lemma lem4352384 {A : Type'} (_49679 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49679.
Proof. exact (EQ_MP (@lem4352381 A s _49679) (@lem4349826 A _49679 s h1)). Qed.
Lemma lem4352385 {A : Type'} (_49679 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49679.
Proof. exact (@lem4352384 A _49679 s h1). Qed.
Lemma lem4352386 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4352385 A x s h1). Qed.
Lemma lem4352389 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : False.
Proof. exact (@lem4352386 A x s h1 (@lem4352376 A B s t s' x t' x' h2 h3)). Qed.
Lemma lem4352390 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352389 A B s t s' x t' x' h1 h2 h3). Qed.
Lemma lem4352392 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352393 : term764 = False.
Proof. exact (@lem4352392 False). Qed.
Lemma lem4352394 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4352393) (@lem4352390 A B s t s' x t' x' h1 h2 h3)). Qed.
Lemma lem4352396 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (proj1 (@lem4344209 A B s x t x' h1)). Qed.
Lemma lem4352397 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4352396 A B s x t x' h1). Qed.
Lemma lem4352399 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352400 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4352399 (s x)). Qed.
Lemma lem4352401 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : s x.
Proof. exact (EQ_MP (@lem4352400 A s x) (@lem4352397 A B s x t x' h1)). Qed.
Lemma lem4352404 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352406 {A : Type'} (s : A -> Prop) (_49682 : A) : (term99 A s _49682) = (term98 A s _49682).
Proof. exact (@lem4352404 (s _49682)). Qed.
Lemma lem4352409 {A : Type'} (_49682 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49682.
Proof. exact (EQ_MP (@lem4352406 A s _49682) (@lem4349848 A _49682 s h1)). Qed.
Lemma lem4352410 {A : Type'} (_49682 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49682.
Proof. exact (@lem4352409 A _49682 s h1). Qed.
Lemma lem4352411 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4352410 A x s h1). Qed.
Lemma lem4352414 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352411 A x s h1 (@lem4352401 A B s x t x' h2)). Qed.
Lemma lem4352415 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352414 A B s x t x' h1 h2). Qed.
Lemma lem4352417 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352418 : term764 = False.
Proof. exact (@lem4352417 False). Qed.
Lemma lem4352419 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352418) (@lem4352415 A B s x t x' h1 h2)). Qed.
Lemma lem4352421 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344198 B t' t x''' h1)). Qed.
Lemma lem4352422 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4352421 B t' t x''' h1). Qed.
Lemma lem4352424 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352425 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4352424 (t' x''')). Qed.
Lemma lem4352426 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4352425 B t' x''') (@lem4352422 B t' t x''' h1)). Qed.
Lemma lem4352432 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352433 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : (term163 B t' t _49684) = (term765 B t t' _49684).
Proof. exact (@lem4352432 (t _49684) (term99 B t' _49684)). Qed.
Lemma lem4352439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352440 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : (term766 B t' t _49684) = (term767 B t t' _49684).
Proof. exact (MK_COMB (@lem4352439) (@lem4352433 B t t' _49684)). Qed.
Lemma lem4352446 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : (term765 B t t' _49684) = (term765 B t t' _49684).
Proof. exact (eq_refl (term765 B t t' _49684)). Qed.
Lemma lem4352447 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : ((term163 B t' t _49684) = (term765 B t t' _49684)) = ((term765 B t t' _49684) = (term765 B t t' _49684)).
Proof. exact (MK_COMB (@lem4352440 B t t' _49684) (@lem4352446 B t t' _49684)). Qed.
Lemma lem4352449 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352450 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352449 Prop x). Qed.
Lemma lem4352451 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : ((term765 B t t' _49684) = (term765 B t t' _49684)) = True.
Proof. exact (@lem4352450 (term765 B t t' _49684)). Qed.
Lemma lem4352452 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : ((term163 B t' t _49684) = (term765 B t t' _49684)) = True.
Proof. exact (TRANS (@lem4352447 B t t' _49684) (@lem4352451 B t t' _49684)). Qed.
Lemma lem4352453 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : True = ((term163 B t' t _49684) = (term765 B t t' _49684)).
Proof. exact (SYM (@lem4352452 B t t' _49684)). Qed.
Lemma lem4352454 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49684 : B) : (term163 B t' t _49684) = (term765 B t t' _49684).
Proof. exact (EQ_MP (@lem4352453 B t t' _49684) (@lem0)). Qed.
Lemma lem4352455 {A B : Type'} (_49684 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 B t t' _49684.
Proof. exact (EQ_MP (@lem4352454 B t t' _49684) (@lem4349868 A B _49684 s' s t' t h1)). Qed.
Lemma lem4352457 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352458 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49684 : B) : (term765 B t t' _49684) = (term769 B t' t _49684).
Proof. exact (@lem4352457 (term99 B t' _49684) (t _49684)). Qed.
Lemma lem4352460 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352461 {B : Type'} (t' : B -> Prop) (_49684 : B) : (term151 B t' _49684) = (t' _49684).
Proof. exact (@lem4352460 (t' _49684)). Qed.
Lemma lem4352462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352463 {B : Type'} (t' : B -> Prop) (_49684 : B) : (term770 B t' _49684) = (term96 B t' _49684).
Proof. exact (MK_COMB (@lem4352462) (@lem4352461 B t' _49684)). Qed.
Lemma lem4352464 {B : Type'} (t : B -> Prop) (_49684 : B) : (t _49684) = (t _49684).
Proof. exact (eq_refl (t _49684)). Qed.
Lemma lem4352465 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49684 : B) : (term769 B t' t _49684) = (term114 B t' t _49684).
Proof. exact (MK_COMB (@lem4352463 B t' _49684) (@lem4352464 B t _49684)). Qed.
Lemma lem4352466 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49684 : B) : (term765 B t t' _49684) = (term114 B t' t _49684).
Proof. exact (TRANS (@lem4352458 B t' t _49684) (@lem4352465 B t' t _49684)). Qed.
Lemma lem4352469 {A B : Type'} (_49684 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49684.
Proof. exact (EQ_MP (@lem4352466 B t' t _49684) (@lem4352455 A B _49684 s' s t' t h1)). Qed.
Lemma lem4352470 {A B : Type'} (_49684 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49684.
Proof. exact (@lem4352469 A B _49684 s' s t' t h1). Qed.
Lemma lem4352471 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t x'''.
Proof. exact (@lem4352470 A B x''' s' s t' t h1). Qed.
Lemma lem4352474 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (@lem4352471 A B x''' s' s t' t h1 (@lem4352426 B t' t x''' h2)). Qed.
Lemma lem4352475 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4352474 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4352477 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352478 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4352477 (t x''')). Qed.
Lemma lem4352479 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (EQ_MP (@lem4352478 B t x''') (@lem4352475 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4352482 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352484 {B : Type'} (t : B -> Prop) (x''' : B) : (term99 B t x''') = (term98 B t x''').
Proof. exact (@lem4352482 (t x''')). Qed.
Lemma lem4352487 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term98 B t x'''.
Proof. exact (EQ_MP (@lem4352484 B t x''') (@lem4349874 B t' t x''' h1)). Qed.
Lemma lem4352490 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (@lem4352487 B t' t x''' h2 (@lem4352479 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4352491 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4352490 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4352493 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352494 : term764 = False.
Proof. exact (@lem4352493 False). Qed.
Lemma lem4352495 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4352494) (@lem4352491 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4352497 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344223 A B s x t x' h1)). Qed.
Lemma lem4352498 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4352497 A B s x t x' h1). Qed.
Lemma lem4352500 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352501 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4352500 (t x')). Qed.
Lemma lem4352502 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4352501 B t x') (@lem4352498 A B s x t x' h1)). Qed.
Lemma lem4352505 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352507 {B : Type'} (t : B -> Prop) (_49688 : B) : (term99 B t _49688) = (term98 B t _49688).
Proof. exact (@lem4352505 (t _49688)). Qed.
Lemma lem4352510 {B : Type'} (_49688 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49688.
Proof. exact (EQ_MP (@lem4352507 B t _49688) (@lem4349892 B _49688 t h1)). Qed.
Lemma lem4352511 {B : Type'} (_49688 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49688.
Proof. exact (@lem4352510 B _49688 t h1). Qed.
Lemma lem4352512 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4352511 B x' t h1). Qed.
Lemma lem4352515 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352512 B x' t h1 (@lem4352502 A B s x t x' h2)). Qed.
Lemma lem4352516 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352515 A B s x t x' h1 h2). Qed.
Lemma lem4352518 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352519 : term764 = False.
Proof. exact (@lem4352518 False). Qed.
Lemma lem4352520 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352519) (@lem4352516 A B s x t x' h1 h2)). Qed.
Lemma lem4352522 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (proj2 (@lem4344224 A B s' x t' x' h1)). Qed.
Lemma lem4352523 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4352522 A B s' x t' x' h1). Qed.
Lemma lem4352525 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352526 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4352525 (t' x')). Qed.
Lemma lem4352527 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term267 A B s' x t' x') : t' x'.
Proof. exact (EQ_MP (@lem4352526 B t' x') (@lem4352523 A B s' x t' x' h1)). Qed.
Lemma lem4352533 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352534 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : (term163 B t' t _49690) = (term765 B t t' _49690).
Proof. exact (@lem4352533 (t _49690) (term99 B t' _49690)). Qed.
Lemma lem4352540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352541 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : (term766 B t' t _49690) = (term767 B t t' _49690).
Proof. exact (MK_COMB (@lem4352540) (@lem4352534 B t t' _49690)). Qed.
Lemma lem4352547 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : (term765 B t t' _49690) = (term765 B t t' _49690).
Proof. exact (eq_refl (term765 B t t' _49690)). Qed.
Lemma lem4352548 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : ((term163 B t' t _49690) = (term765 B t t' _49690)) = ((term765 B t t' _49690) = (term765 B t t' _49690)).
Proof. exact (MK_COMB (@lem4352541 B t t' _49690) (@lem4352547 B t t' _49690)). Qed.
Lemma lem4352550 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352551 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352550 Prop x). Qed.
Lemma lem4352552 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : ((term765 B t t' _49690) = (term765 B t t' _49690)) = True.
Proof. exact (@lem4352551 (term765 B t t' _49690)). Qed.
Lemma lem4352553 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : ((term163 B t' t _49690) = (term765 B t t' _49690)) = True.
Proof. exact (TRANS (@lem4352548 B t t' _49690) (@lem4352552 B t t' _49690)). Qed.
Lemma lem4352554 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : True = ((term163 B t' t _49690) = (term765 B t t' _49690)).
Proof. exact (SYM (@lem4352553 B t t' _49690)). Qed.
Lemma lem4352555 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49690 : B) : (term163 B t' t _49690) = (term765 B t t' _49690).
Proof. exact (EQ_MP (@lem4352554 B t t' _49690) (@lem0)). Qed.
Lemma lem4352556 {A B : Type'} (_49690 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 B t t' _49690.
Proof. exact (EQ_MP (@lem4352555 B t t' _49690) (@lem4349912 A B _49690 s' s t' t h1)). Qed.
Lemma lem4352558 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352559 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49690 : B) : (term765 B t t' _49690) = (term769 B t' t _49690).
Proof. exact (@lem4352558 (term99 B t' _49690) (t _49690)). Qed.
Lemma lem4352561 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352562 {B : Type'} (t' : B -> Prop) (_49690 : B) : (term151 B t' _49690) = (t' _49690).
Proof. exact (@lem4352561 (t' _49690)). Qed.
Lemma lem4352563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352564 {B : Type'} (t' : B -> Prop) (_49690 : B) : (term770 B t' _49690) = (term96 B t' _49690).
Proof. exact (MK_COMB (@lem4352563) (@lem4352562 B t' _49690)). Qed.
Lemma lem4352565 {B : Type'} (t : B -> Prop) (_49690 : B) : (t _49690) = (t _49690).
Proof. exact (eq_refl (t _49690)). Qed.
Lemma lem4352566 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49690 : B) : (term769 B t' t _49690) = (term114 B t' t _49690).
Proof. exact (MK_COMB (@lem4352564 B t' _49690) (@lem4352565 B t _49690)). Qed.
Lemma lem4352567 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49690 : B) : (term765 B t t' _49690) = (term114 B t' t _49690).
Proof. exact (TRANS (@lem4352559 B t' t _49690) (@lem4352566 B t' t _49690)). Qed.
Lemma lem4352570 {A B : Type'} (_49690 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49690.
Proof. exact (EQ_MP (@lem4352567 B t' t _49690) (@lem4352556 A B _49690 s' s t' t h1)). Qed.
Lemma lem4352571 {A B : Type'} (_49690 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49690.
Proof. exact (@lem4352570 A B _49690 s' s t' t h1). Qed.
Lemma lem4352572 {A B : Type'} (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t x'.
Proof. exact (@lem4352571 A B x' s' s t' t h1). Qed.
Lemma lem4352575 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term179 A B s' s t' t) (h2 : term267 A B s' x t' x') : t x'.
Proof. exact (@lem4352572 A B x' s' s t' t h1 (@lem4352527 A B s' x t' x' h2)). Qed.
Lemma lem4352576 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term179 A B s' s t' t) (h2 : term267 A B s' x t' x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4352575 A B s t s' x t' x' h1 h2). Qed.
Lemma lem4352578 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352579 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4352578 (t x')). Qed.
Lemma lem4352580 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term179 A B s' s t' t) (h2 : term267 A B s' x t' x') : t x'.
Proof. exact (EQ_MP (@lem4352579 B t x') (@lem4352576 A B s t s' x t' x' h1 h2)). Qed.
Lemma lem4352583 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352585 {B : Type'} (t : B -> Prop) (_49691 : B) : (term99 B t _49691) = (term98 B t _49691).
Proof. exact (@lem4352583 (t _49691)). Qed.
Lemma lem4352588 {B : Type'} (_49691 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49691.
Proof. exact (EQ_MP (@lem4352585 B t _49691) (@lem4349914 B _49691 t h1)). Qed.
Lemma lem4352589 {B : Type'} (_49691 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49691.
Proof. exact (@lem4352588 B _49691 t h1). Qed.
Lemma lem4352590 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4352589 B x' t h1). Qed.
Lemma lem4352593 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : False.
Proof. exact (@lem4352590 B x' t h1 (@lem4352580 A B s t s' x t' x' h2 h3)). Qed.
Lemma lem4352594 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352593 A B s t s' x t' x' h1 h2 h3). Qed.
Lemma lem4352596 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352597 : term764 = False.
Proof. exact (@lem4352596 False). Qed.
Lemma lem4352598 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4352597) (@lem4352594 A B s t s' x t' x' h1 h2 h3)). Qed.
Lemma lem4352600 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344231 A B s x t x' h1)). Qed.
Lemma lem4352601 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4352600 A B s x t x' h1). Qed.
Lemma lem4352603 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352604 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4352603 (t x')). Qed.
Lemma lem4352605 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4352604 B t x') (@lem4352601 A B s x t x' h1)). Qed.
Lemma lem4352608 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352610 {B : Type'} (t : B -> Prop) (_49694 : B) : (term99 B t _49694) = (term98 B t _49694).
Proof. exact (@lem4352608 (t _49694)). Qed.
Lemma lem4352613 {B : Type'} (_49694 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49694.
Proof. exact (EQ_MP (@lem4352610 B t _49694) (@lem4349936 B _49694 t h1)). Qed.
Lemma lem4352614 {B : Type'} (_49694 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49694.
Proof. exact (@lem4352613 B _49694 t h1). Qed.
Lemma lem4352615 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4352614 B x' t h1). Qed.
Lemma lem4352618 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352615 B x' t h1 (@lem4352605 A B s x t x' h2)). Qed.
Lemma lem4352619 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352618 A B s x t x' h1 h2). Qed.
Lemma lem4352621 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352622 : term764 = False.
Proof. exact (@lem4352621 False). Qed.
Lemma lem4352623 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352622) (@lem4352619 A B s x t x' h1 h2)). Qed.
Lemma lem4352625 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344220 A s' s x'' h1)). Qed.
Lemma lem4352626 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4352625 A s' s x'' h1). Qed.
Lemma lem4352628 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352629 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4352628 (s' x'')). Qed.
Lemma lem4352630 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4352629 A s' x'') (@lem4352626 A s' s x'' h1)). Qed.
Lemma lem4352636 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352637 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : (term163 A s' s _49695) = (term765 A s s' _49695).
Proof. exact (@lem4352636 (s _49695) (term99 A s' _49695)). Qed.
Lemma lem4352643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352644 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : (term766 A s' s _49695) = (term767 A s s' _49695).
Proof. exact (MK_COMB (@lem4352643) (@lem4352637 A s s' _49695)). Qed.
Lemma lem4352650 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : (term765 A s s' _49695) = (term765 A s s' _49695).
Proof. exact (eq_refl (term765 A s s' _49695)). Qed.
Lemma lem4352651 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : ((term163 A s' s _49695) = (term765 A s s' _49695)) = ((term765 A s s' _49695) = (term765 A s s' _49695)).
Proof. exact (MK_COMB (@lem4352644 A s s' _49695) (@lem4352650 A s s' _49695)). Qed.
Lemma lem4352653 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352654 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352653 Prop x). Qed.
Lemma lem4352655 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : ((term765 A s s' _49695) = (term765 A s s' _49695)) = True.
Proof. exact (@lem4352654 (term765 A s s' _49695)). Qed.
Lemma lem4352656 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : ((term163 A s' s _49695) = (term765 A s s' _49695)) = True.
Proof. exact (TRANS (@lem4352651 A s s' _49695) (@lem4352655 A s s' _49695)). Qed.
Lemma lem4352657 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : True = ((term163 A s' s _49695) = (term765 A s s' _49695)).
Proof. exact (SYM (@lem4352656 A s s' _49695)). Qed.
Lemma lem4352658 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49695 : A) : (term163 A s' s _49695) = (term765 A s s' _49695).
Proof. exact (EQ_MP (@lem4352657 A s s' _49695) (@lem0)). Qed.
Lemma lem4352659 {A B : Type'} (_49695 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 A s s' _49695.
Proof. exact (EQ_MP (@lem4352658 A s s' _49695) (@lem4349950 A B _49695 s' s t' t h1)). Qed.
Lemma lem4352661 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352662 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49695 : A) : (term765 A s s' _49695) = (term769 A s' s _49695).
Proof. exact (@lem4352661 (term99 A s' _49695) (s _49695)). Qed.
Lemma lem4352664 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352665 {A : Type'} (s' : A -> Prop) (_49695 : A) : (term151 A s' _49695) = (s' _49695).
Proof. exact (@lem4352664 (s' _49695)). Qed.
Lemma lem4352666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352667 {A : Type'} (s' : A -> Prop) (_49695 : A) : (term770 A s' _49695) = (term96 A s' _49695).
Proof. exact (MK_COMB (@lem4352666) (@lem4352665 A s' _49695)). Qed.
Lemma lem4352668 {A : Type'} (s : A -> Prop) (_49695 : A) : (s _49695) = (s _49695).
Proof. exact (eq_refl (s _49695)). Qed.
Lemma lem4352669 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49695 : A) : (term769 A s' s _49695) = (term114 A s' s _49695).
Proof. exact (MK_COMB (@lem4352667 A s' _49695) (@lem4352668 A s _49695)). Qed.
Lemma lem4352670 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49695 : A) : (term765 A s s' _49695) = (term114 A s' s _49695).
Proof. exact (TRANS (@lem4352662 A s' s _49695) (@lem4352669 A s' s _49695)). Qed.
Lemma lem4352673 {A B : Type'} (_49695 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49695.
Proof. exact (EQ_MP (@lem4352670 A s' s _49695) (@lem4352659 A B _49695 s' s t' t h1)). Qed.
Lemma lem4352674 {A B : Type'} (_49695 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49695.
Proof. exact (@lem4352673 A B _49695 s' s t' t h1). Qed.
Lemma lem4352675 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s x''.
Proof. exact (@lem4352674 A B x'' s' s t' t h1). Qed.
Lemma lem4352678 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (@lem4352675 A B x'' s' s t' t h1 (@lem4352630 A s' s x'' h2)). Qed.
Lemma lem4352679 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4352678 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4352681 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352682 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4352681 (s x'')). Qed.
Lemma lem4352683 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (EQ_MP (@lem4352682 A s x'') (@lem4352679 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4352686 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352688 {A : Type'} (s : A -> Prop) (x'' : A) : (term99 A s x'') = (term98 A s x'').
Proof. exact (@lem4352686 (s x'')). Qed.
Lemma lem4352691 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term98 A s x''.
Proof. exact (EQ_MP (@lem4352688 A s x'') (@lem4349962 A s' s x'' h1)). Qed.
Lemma lem4352694 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (@lem4352691 A s' s x'' h2 (@lem4352683 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4352695 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4352694 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4352697 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352698 : term764 = False.
Proof. exact (@lem4352697 False). Qed.
Lemma lem4352699 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4352698) (@lem4352695 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4352701 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344241 A B s x t x' h1)). Qed.
Lemma lem4352702 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4352701 A B s x t x' h1). Qed.
Lemma lem4352704 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352705 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4352704 (t x')). Qed.
Lemma lem4352706 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4352705 B t x') (@lem4352702 A B s x t x' h1)). Qed.
Lemma lem4352709 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352711 {B : Type'} (t : B -> Prop) (_49700 : B) : (term99 B t _49700) = (term98 B t _49700).
Proof. exact (@lem4352709 (t _49700)). Qed.
Lemma lem4352714 {B : Type'} (_49700 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49700.
Proof. exact (EQ_MP (@lem4352711 B t _49700) (@lem4349980 B _49700 t h1)). Qed.
Lemma lem4352715 {B : Type'} (_49700 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49700.
Proof. exact (@lem4352714 B _49700 t h1). Qed.
Lemma lem4352716 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4352715 B x' t h1). Qed.
Lemma lem4352719 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352716 B x' t h1 (@lem4352706 A B s x t x' h2)). Qed.
Lemma lem4352720 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352719 A B s x t x' h1 h2). Qed.
Lemma lem4352722 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352723 : term764 = False.
Proof. exact (@lem4352722 False). Qed.
Lemma lem4352724 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352723) (@lem4352720 A B s x t x' h1 h2)). Qed.
Lemma lem4352726 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344237 B t t' x''' h1)). Qed.
Lemma lem4352727 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4352726 B t t' x''' h1). Qed.
Lemma lem4352729 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352730 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4352729 (t x''')). Qed.
Lemma lem4352731 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4352730 B t x''') (@lem4352727 B t t' x''' h1)). Qed.
Lemma lem4352734 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352736 {B : Type'} (t : B -> Prop) (_49703 : B) : (term99 B t _49703) = (term98 B t _49703).
Proof. exact (@lem4352734 (t _49703)). Qed.
Lemma lem4352739 {B : Type'} (_49703 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49703.
Proof. exact (EQ_MP (@lem4352736 B t _49703) (@lem4350002 B _49703 t h1)). Qed.
Lemma lem4352740 {B : Type'} (_49703 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49703.
Proof. exact (@lem4352739 B _49703 t h1). Qed.
Lemma lem4352741 {B : Type'} (x''' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'''.
Proof. exact (@lem4352740 B x''' t h1). Qed.
Lemma lem4352744 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4352741 B x''' t h1 (@lem4352731 B t t' x''' h2)). Qed.
Lemma lem4352745 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4352744 B t t' x''' h1 h2). Qed.
Lemma lem4352747 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352748 : term764 = False.
Proof. exact (@lem4352747 False). Qed.
Lemma lem4352749 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4352748) (@lem4352745 B t t' x''' h1 h2)). Qed.
Lemma lem4352751 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (proj2 (@lem4344249 A B s x t x' h1)). Qed.
Lemma lem4352752 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4352751 A B s x t x' h1). Qed.
Lemma lem4352754 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352755 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4352754 (t x')). Qed.
Lemma lem4352756 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term267 A B s x t x') : t x'.
Proof. exact (EQ_MP (@lem4352755 B t x') (@lem4352752 A B s x t x' h1)). Qed.
Lemma lem4352759 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352761 {B : Type'} (t : B -> Prop) (_49706 : B) : (term99 B t _49706) = (term98 B t _49706).
Proof. exact (@lem4352759 (t _49706)). Qed.
Lemma lem4352764 {B : Type'} (_49706 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49706.
Proof. exact (EQ_MP (@lem4352761 B t _49706) (@lem4350024 B _49706 t h1)). Qed.
Lemma lem4352765 {B : Type'} (_49706 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49706.
Proof. exact (@lem4352764 B _49706 t h1). Qed.
Lemma lem4352766 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4352765 B x' t h1). Qed.
Lemma lem4352769 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (@lem4352766 B x' t h1 (@lem4352756 A B s x t x' h2)). Qed.
Lemma lem4352770 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : term764.
Proof. exact (fun h0 : ~ False => @lem4352769 A B s x t x' h1 h2). Qed.
Lemma lem4352772 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352773 : term764 = False.
Proof. exact (@lem4352772 False). Qed.
Lemma lem4352774 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4352773) (@lem4352770 A B s x t x' h1 h2)). Qed.
Lemma lem4352776 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344238 B t' t x''' h1)). Qed.
Lemma lem4352777 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4352776 B t' t x''' h1). Qed.
Lemma lem4352779 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352780 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4352779 (t' x''')). Qed.
Lemma lem4352781 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4352780 B t' x''') (@lem4352777 B t' t x''' h1)). Qed.
Lemma lem4352787 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352788 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : (term163 B t' t _49708) = (term765 B t t' _49708).
Proof. exact (@lem4352787 (t _49708) (term99 B t' _49708)). Qed.
Lemma lem4352794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352795 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : (term766 B t' t _49708) = (term767 B t t' _49708).
Proof. exact (MK_COMB (@lem4352794) (@lem4352788 B t t' _49708)). Qed.
Lemma lem4352801 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : (term765 B t t' _49708) = (term765 B t t' _49708).
Proof. exact (eq_refl (term765 B t t' _49708)). Qed.
Lemma lem4352802 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : ((term163 B t' t _49708) = (term765 B t t' _49708)) = ((term765 B t t' _49708) = (term765 B t t' _49708)).
Proof. exact (MK_COMB (@lem4352795 B t t' _49708) (@lem4352801 B t t' _49708)). Qed.
Lemma lem4352804 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352805 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352804 Prop x). Qed.
Lemma lem4352806 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : ((term765 B t t' _49708) = (term765 B t t' _49708)) = True.
Proof. exact (@lem4352805 (term765 B t t' _49708)). Qed.
Lemma lem4352807 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : ((term163 B t' t _49708) = (term765 B t t' _49708)) = True.
Proof. exact (TRANS (@lem4352802 B t t' _49708) (@lem4352806 B t t' _49708)). Qed.
Lemma lem4352808 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : True = ((term163 B t' t _49708) = (term765 B t t' _49708)).
Proof. exact (SYM (@lem4352807 B t t' _49708)). Qed.
Lemma lem4352809 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49708 : B) : (term163 B t' t _49708) = (term765 B t t' _49708).
Proof. exact (EQ_MP (@lem4352808 B t t' _49708) (@lem0)). Qed.
Lemma lem4352810 {A B : Type'} (_49708 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 B t t' _49708.
Proof. exact (EQ_MP (@lem4352809 B t t' _49708) (@lem4350044 A B _49708 s' s t' t h1)). Qed.
Lemma lem4352812 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352813 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49708 : B) : (term765 B t t' _49708) = (term769 B t' t _49708).
Proof. exact (@lem4352812 (term99 B t' _49708) (t _49708)). Qed.
Lemma lem4352815 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352816 {B : Type'} (t' : B -> Prop) (_49708 : B) : (term151 B t' _49708) = (t' _49708).
Proof. exact (@lem4352815 (t' _49708)). Qed.
Lemma lem4352817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352818 {B : Type'} (t' : B -> Prop) (_49708 : B) : (term770 B t' _49708) = (term96 B t' _49708).
Proof. exact (MK_COMB (@lem4352817) (@lem4352816 B t' _49708)). Qed.
Lemma lem4352819 {B : Type'} (t : B -> Prop) (_49708 : B) : (t _49708) = (t _49708).
Proof. exact (eq_refl (t _49708)). Qed.
Lemma lem4352820 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49708 : B) : (term769 B t' t _49708) = (term114 B t' t _49708).
Proof. exact (MK_COMB (@lem4352818 B t' _49708) (@lem4352819 B t _49708)). Qed.
Lemma lem4352821 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49708 : B) : (term765 B t t' _49708) = (term114 B t' t _49708).
Proof. exact (TRANS (@lem4352813 B t' t _49708) (@lem4352820 B t' t _49708)). Qed.
Lemma lem4352824 {A B : Type'} (_49708 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49708.
Proof. exact (EQ_MP (@lem4352821 B t' t _49708) (@lem4352810 A B _49708 s' s t' t h1)). Qed.
Lemma lem4352825 {A B : Type'} (_49708 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49708.
Proof. exact (@lem4352824 A B _49708 s' s t' t h1). Qed.
Lemma lem4352826 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t x'''.
Proof. exact (@lem4352825 A B x''' s' s t' t h1). Qed.
Lemma lem4352829 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (@lem4352826 A B x''' s' s t' t h1 (@lem4352781 B t' t x''' h2)). Qed.
Lemma lem4352830 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4352829 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4352832 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352833 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4352832 (t x''')). Qed.
Lemma lem4352834 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (EQ_MP (@lem4352833 B t x''') (@lem4352830 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4352837 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352839 {B : Type'} (t : B -> Prop) (x''' : B) : (term99 B t x''') = (term98 B t x''').
Proof. exact (@lem4352837 (t x''')). Qed.
Lemma lem4352842 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term98 B t x'''.
Proof. exact (EQ_MP (@lem4352839 B t x''') (@lem4350050 B t' t x''' h1)). Qed.
Lemma lem4352845 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (@lem4352842 B t' t x''' h2 (@lem4352834 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4352846 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4352845 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4352848 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352849 : term764 = False.
Proof. exact (@lem4352848 False). Qed.
Lemma lem4352850 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4352849) (@lem4352846 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4352852 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344259 A s s' x'' h1)). Qed.
Lemma lem4352853 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4352852 A s s' x'' h1). Qed.
Lemma lem4352855 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352856 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4352855 (s x'')). Qed.
Lemma lem4352857 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4352856 A s x'') (@lem4352853 A s s' x'' h1)). Qed.
Lemma lem4352863 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352864 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : (term163 A s s' _49712) = (term765 A s' s _49712).
Proof. exact (@lem4352863 (s' _49712) (term99 A s _49712)). Qed.
Lemma lem4352870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352871 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : (term766 A s s' _49712) = (term767 A s' s _49712).
Proof. exact (MK_COMB (@lem4352870) (@lem4352864 A s' s _49712)). Qed.
Lemma lem4352877 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : (term765 A s' s _49712) = (term765 A s' s _49712).
Proof. exact (eq_refl (term765 A s' s _49712)). Qed.
Lemma lem4352878 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : ((term163 A s s' _49712) = (term765 A s' s _49712)) = ((term765 A s' s _49712) = (term765 A s' s _49712)).
Proof. exact (MK_COMB (@lem4352871 A s' s _49712) (@lem4352877 A s' s _49712)). Qed.
Lemma lem4352880 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352881 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352880 Prop x). Qed.
Lemma lem4352882 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : ((term765 A s' s _49712) = (term765 A s' s _49712)) = True.
Proof. exact (@lem4352881 (term765 A s' s _49712)). Qed.
Lemma lem4352883 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : ((term163 A s s' _49712) = (term765 A s' s _49712)) = True.
Proof. exact (TRANS (@lem4352878 A s' s _49712) (@lem4352882 A s' s _49712)). Qed.
Lemma lem4352884 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : True = ((term163 A s s' _49712) = (term765 A s' s _49712)).
Proof. exact (SYM (@lem4352883 A s' s _49712)). Qed.
Lemma lem4352885 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49712 : A) : (term163 A s s' _49712) = (term765 A s' s _49712).
Proof. exact (EQ_MP (@lem4352884 A s' s _49712) (@lem0)). Qed.
Lemma lem4352886 {A B : Type'} (_49712 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 A s' s _49712.
Proof. exact (EQ_MP (@lem4352885 A s' s _49712) (@lem4350072 A B _49712 s s' t t' h1)). Qed.
Lemma lem4352888 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352889 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49712 : A) : (term765 A s' s _49712) = (term769 A s s' _49712).
Proof. exact (@lem4352888 (term99 A s _49712) (s' _49712)). Qed.
Lemma lem4352891 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352892 {A : Type'} (s : A -> Prop) (_49712 : A) : (term151 A s _49712) = (s _49712).
Proof. exact (@lem4352891 (s _49712)). Qed.
Lemma lem4352893 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352894 {A : Type'} (s : A -> Prop) (_49712 : A) : (term770 A s _49712) = (term96 A s _49712).
Proof. exact (MK_COMB (@lem4352893) (@lem4352892 A s _49712)). Qed.
Lemma lem4352895 {A : Type'} (s' : A -> Prop) (_49712 : A) : (s' _49712) = (s' _49712).
Proof. exact (eq_refl (s' _49712)). Qed.
Lemma lem4352896 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49712 : A) : (term769 A s s' _49712) = (term114 A s s' _49712).
Proof. exact (MK_COMB (@lem4352894 A s _49712) (@lem4352895 A s' _49712)). Qed.
Lemma lem4352897 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49712 : A) : (term765 A s' s _49712) = (term114 A s s' _49712).
Proof. exact (TRANS (@lem4352889 A s s' _49712) (@lem4352896 A s s' _49712)). Qed.
Lemma lem4352900 {A B : Type'} (_49712 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49712.
Proof. exact (EQ_MP (@lem4352897 A s s' _49712) (@lem4352886 A B _49712 s s' t t' h1)). Qed.
Lemma lem4352901 {A B : Type'} (_49712 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49712.
Proof. exact (@lem4352900 A B _49712 s s' t t' h1). Qed.
Lemma lem4352902 {A B : Type'} (x'' : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' x''.
Proof. exact (@lem4352901 A B x'' s s' t t' h1). Qed.
Lemma lem4352905 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (@lem4352902 A B x'' s s' t t' h1 (@lem4352857 A s s' x'' h2)). Qed.
Lemma lem4352906 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4352905 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4352908 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352909 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4352908 (s' x'')). Qed.
Lemma lem4352910 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (EQ_MP (@lem4352909 A s' x'') (@lem4352906 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4352913 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352915 {A : Type'} (s' : A -> Prop) (x'' : A) : (term99 A s' x'') = (term98 A s' x'').
Proof. exact (@lem4352913 (s' x'')). Qed.
Lemma lem4352918 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term98 A s' x''.
Proof. exact (EQ_MP (@lem4352915 A s' x'') (@lem4350082 A s s' x'' h1)). Qed.
Lemma lem4352921 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4352918 A s s' x'' h2 (@lem4352910 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4352922 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4352921 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4352924 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352925 : term764 = False.
Proof. exact (@lem4352924 False). Qed.
Lemma lem4352926 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4352925) (@lem4352922 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4352928 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344259 A s s' x'' h1)). Qed.
Lemma lem4352929 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4352928 A s s' x'' h1). Qed.
Lemma lem4352931 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352932 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4352931 (s x'')). Qed.
Lemma lem4352933 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4352932 A s x'') (@lem4352929 A s s' x'' h1)). Qed.
Lemma lem4352939 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4352940 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : (term163 A s s' _49716) = (term765 A s' s _49716).
Proof. exact (@lem4352939 (s' _49716) (term99 A s _49716)). Qed.
Lemma lem4352946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4352947 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : (term766 A s s' _49716) = (term767 A s' s _49716).
Proof. exact (MK_COMB (@lem4352946) (@lem4352940 A s' s _49716)). Qed.
Lemma lem4352953 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : (term765 A s' s _49716) = (term765 A s' s _49716).
Proof. exact (eq_refl (term765 A s' s _49716)). Qed.
Lemma lem4352954 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : ((term163 A s s' _49716) = (term765 A s' s _49716)) = ((term765 A s' s _49716) = (term765 A s' s _49716)).
Proof. exact (MK_COMB (@lem4352947 A s' s _49716) (@lem4352953 A s' s _49716)). Qed.
Lemma lem4352956 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4352957 (x : Prop) : (x = x) = True.
Proof. exact (@lem4352956 Prop x). Qed.
Lemma lem4352958 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : ((term765 A s' s _49716) = (term765 A s' s _49716)) = True.
Proof. exact (@lem4352957 (term765 A s' s _49716)). Qed.
Lemma lem4352959 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : ((term163 A s s' _49716) = (term765 A s' s _49716)) = True.
Proof. exact (TRANS (@lem4352954 A s' s _49716) (@lem4352958 A s' s _49716)). Qed.
Lemma lem4352960 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : True = ((term163 A s s' _49716) = (term765 A s' s _49716)).
Proof. exact (SYM (@lem4352959 A s' s _49716)). Qed.
Lemma lem4352961 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49716 : A) : (term163 A s s' _49716) = (term765 A s' s _49716).
Proof. exact (EQ_MP (@lem4352960 A s' s _49716) (@lem0)). Qed.
Lemma lem4352962 {A B : Type'} (_49716 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 A s' s _49716.
Proof. exact (EQ_MP (@lem4352961 A s' s _49716) (@lem4350104 A B _49716 s s' t t' h1)). Qed.
Lemma lem4352964 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4352965 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49716 : A) : (term765 A s' s _49716) = (term769 A s s' _49716).
Proof. exact (@lem4352964 (term99 A s _49716) (s' _49716)). Qed.
Lemma lem4352967 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4352968 {A : Type'} (s : A -> Prop) (_49716 : A) : (term151 A s _49716) = (s _49716).
Proof. exact (@lem4352967 (s _49716)). Qed.
Lemma lem4352969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4352970 {A : Type'} (s : A -> Prop) (_49716 : A) : (term770 A s _49716) = (term96 A s _49716).
Proof. exact (MK_COMB (@lem4352969) (@lem4352968 A s _49716)). Qed.
Lemma lem4352971 {A : Type'} (s' : A -> Prop) (_49716 : A) : (s' _49716) = (s' _49716).
Proof. exact (eq_refl (s' _49716)). Qed.
Lemma lem4352972 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49716 : A) : (term769 A s s' _49716) = (term114 A s s' _49716).
Proof. exact (MK_COMB (@lem4352970 A s _49716) (@lem4352971 A s' _49716)). Qed.
Lemma lem4352973 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49716 : A) : (term765 A s' s _49716) = (term114 A s s' _49716).
Proof. exact (TRANS (@lem4352965 A s s' _49716) (@lem4352972 A s s' _49716)). Qed.
Lemma lem4352976 {A B : Type'} (_49716 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49716.
Proof. exact (EQ_MP (@lem4352973 A s s' _49716) (@lem4352962 A B _49716 s s' t t' h1)). Qed.
Lemma lem4352977 {A B : Type'} (_49716 : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' _49716.
Proof. exact (@lem4352976 A B _49716 s s' t t' h1). Qed.
Lemma lem4352978 {A B : Type'} (x'' : A) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 A s s' x''.
Proof. exact (@lem4352977 A B x'' s s' t t' h1). Qed.
Lemma lem4352981 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (@lem4352978 A B x'' s s' t t' h1 (@lem4352933 A s s' x'' h2)). Qed.
Lemma lem4352982 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4352981 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4352984 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4352985 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4352984 (s' x'')). Qed.
Lemma lem4352986 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : s' x''.
Proof. exact (EQ_MP (@lem4352985 A s' x'') (@lem4352982 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4352989 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4352991 {A : Type'} (s' : A -> Prop) (x'' : A) : (term99 A s' x'') = (term98 A s' x'').
Proof. exact (@lem4352989 (s' x'')). Qed.
Lemma lem4352994 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term98 A s' x''.
Proof. exact (EQ_MP (@lem4352991 A s' x'') (@lem4350114 A s s' x'' h1)). Qed.
Lemma lem4352997 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4352994 A s s' x'' h2 (@lem4352986 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4352998 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4352997 A B t t' s s' x'' h1 h2). Qed.
Lemma lem4353000 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353001 : term764 = False.
Proof. exact (@lem4353000 False). Qed.
Lemma lem4353002 {A B : Type'} (t : B -> Prop) (t' : B -> Prop) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4353001) (@lem4352998 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4353004 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344260 A s' s x'' h1)). Qed.
Lemma lem4353005 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4353004 A s' s x'' h1). Qed.
Lemma lem4353007 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353008 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4353007 (s' x'')). Qed.
Lemma lem4353009 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4353008 A s' x'') (@lem4353005 A s' s x'' h1)). Qed.
Lemma lem4353015 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353016 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : (term163 A s' s _49718) = (term765 A s s' _49718).
Proof. exact (@lem4353015 (s _49718) (term99 A s' _49718)). Qed.
Lemma lem4353022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353023 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : (term766 A s' s _49718) = (term767 A s s' _49718).
Proof. exact (MK_COMB (@lem4353022) (@lem4353016 A s s' _49718)). Qed.
Lemma lem4353029 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : (term765 A s s' _49718) = (term765 A s s' _49718).
Proof. exact (eq_refl (term765 A s s' _49718)). Qed.
Lemma lem4353030 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : ((term163 A s' s _49718) = (term765 A s s' _49718)) = ((term765 A s s' _49718) = (term765 A s s' _49718)).
Proof. exact (MK_COMB (@lem4353023 A s s' _49718) (@lem4353029 A s s' _49718)). Qed.
Lemma lem4353032 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353033 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353032 Prop x). Qed.
Lemma lem4353034 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : ((term765 A s s' _49718) = (term765 A s s' _49718)) = True.
Proof. exact (@lem4353033 (term765 A s s' _49718)). Qed.
Lemma lem4353035 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : ((term163 A s' s _49718) = (term765 A s s' _49718)) = True.
Proof. exact (TRANS (@lem4353030 A s s' _49718) (@lem4353034 A s s' _49718)). Qed.
Lemma lem4353036 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : True = ((term163 A s' s _49718) = (term765 A s s' _49718)).
Proof. exact (SYM (@lem4353035 A s s' _49718)). Qed.
Lemma lem4353037 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49718 : A) : (term163 A s' s _49718) = (term765 A s s' _49718).
Proof. exact (EQ_MP (@lem4353036 A s s' _49718) (@lem0)). Qed.
Lemma lem4353038 {A B : Type'} (_49718 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 A s s' _49718.
Proof. exact (EQ_MP (@lem4353037 A s s' _49718) (@lem4350124 A B _49718 s' s t' t h1)). Qed.
Lemma lem4353040 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353041 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49718 : A) : (term765 A s s' _49718) = (term769 A s' s _49718).
Proof. exact (@lem4353040 (term99 A s' _49718) (s _49718)). Qed.
Lemma lem4353043 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353044 {A : Type'} (s' : A -> Prop) (_49718 : A) : (term151 A s' _49718) = (s' _49718).
Proof. exact (@lem4353043 (s' _49718)). Qed.
Lemma lem4353045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353046 {A : Type'} (s' : A -> Prop) (_49718 : A) : (term770 A s' _49718) = (term96 A s' _49718).
Proof. exact (MK_COMB (@lem4353045) (@lem4353044 A s' _49718)). Qed.
Lemma lem4353047 {A : Type'} (s : A -> Prop) (_49718 : A) : (s _49718) = (s _49718).
Proof. exact (eq_refl (s _49718)). Qed.
Lemma lem4353048 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49718 : A) : (term769 A s' s _49718) = (term114 A s' s _49718).
Proof. exact (MK_COMB (@lem4353046 A s' _49718) (@lem4353047 A s _49718)). Qed.
Lemma lem4353049 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49718 : A) : (term765 A s s' _49718) = (term114 A s' s _49718).
Proof. exact (TRANS (@lem4353041 A s' s _49718) (@lem4353048 A s' s _49718)). Qed.
Lemma lem4353052 {A B : Type'} (_49718 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49718.
Proof. exact (EQ_MP (@lem4353049 A s' s _49718) (@lem4353038 A B _49718 s' s t' t h1)). Qed.
Lemma lem4353053 {A B : Type'} (_49718 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49718.
Proof. exact (@lem4353052 A B _49718 s' s t' t h1). Qed.
Lemma lem4353054 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s x''.
Proof. exact (@lem4353053 A B x'' s' s t' t h1). Qed.
Lemma lem4353057 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (@lem4353054 A B x'' s' s t' t h1 (@lem4353009 A s' s x'' h2)). Qed.
Lemma lem4353058 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4353057 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4353060 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353061 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4353060 (s x'')). Qed.
Lemma lem4353062 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (EQ_MP (@lem4353061 A s x'') (@lem4353058 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4353065 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353067 {A : Type'} (s : A -> Prop) (x'' : A) : (term99 A s x'') = (term98 A s x'').
Proof. exact (@lem4353065 (s x'')). Qed.
Lemma lem4353070 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term98 A s x''.
Proof. exact (EQ_MP (@lem4353067 A s x'') (@lem4350146 A s' s x'' h1)). Qed.
Lemma lem4353073 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (@lem4353070 A s' s x'' h2 (@lem4353062 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4353074 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4353073 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4353076 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353077 : term764 = False.
Proof. exact (@lem4353076 False). Qed.
Lemma lem4353078 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4353077) (@lem4353074 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4353080 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344260 A s' s x'' h1)). Qed.
Lemma lem4353081 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4353080 A s' s x'' h1). Qed.
Lemma lem4353083 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353084 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4353083 (s' x'')). Qed.
Lemma lem4353085 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4353084 A s' x'') (@lem4353081 A s' s x'' h1)). Qed.
Lemma lem4353091 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353092 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : (term163 A s' s _49722) = (term765 A s s' _49722).
Proof. exact (@lem4353091 (s _49722) (term99 A s' _49722)). Qed.
Lemma lem4353098 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353099 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : (term766 A s' s _49722) = (term767 A s s' _49722).
Proof. exact (MK_COMB (@lem4353098) (@lem4353092 A s s' _49722)). Qed.
Lemma lem4353105 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : (term765 A s s' _49722) = (term765 A s s' _49722).
Proof. exact (eq_refl (term765 A s s' _49722)). Qed.
Lemma lem4353106 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : ((term163 A s' s _49722) = (term765 A s s' _49722)) = ((term765 A s s' _49722) = (term765 A s s' _49722)).
Proof. exact (MK_COMB (@lem4353099 A s s' _49722) (@lem4353105 A s s' _49722)). Qed.
Lemma lem4353108 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353109 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353108 Prop x). Qed.
Lemma lem4353110 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : ((term765 A s s' _49722) = (term765 A s s' _49722)) = True.
Proof. exact (@lem4353109 (term765 A s s' _49722)). Qed.
Lemma lem4353111 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : ((term163 A s' s _49722) = (term765 A s s' _49722)) = True.
Proof. exact (TRANS (@lem4353106 A s s' _49722) (@lem4353110 A s s' _49722)). Qed.
Lemma lem4353112 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : True = ((term163 A s' s _49722) = (term765 A s s' _49722)).
Proof. exact (SYM (@lem4353111 A s s' _49722)). Qed.
Lemma lem4353113 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49722 : A) : (term163 A s' s _49722) = (term765 A s s' _49722).
Proof. exact (EQ_MP (@lem4353112 A s s' _49722) (@lem0)). Qed.
Lemma lem4353114 {A B : Type'} (_49722 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 A s s' _49722.
Proof. exact (EQ_MP (@lem4353113 A s s' _49722) (@lem4350156 A B _49722 s' s t' t h1)). Qed.
Lemma lem4353116 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353117 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49722 : A) : (term765 A s s' _49722) = (term769 A s' s _49722).
Proof. exact (@lem4353116 (term99 A s' _49722) (s _49722)). Qed.
Lemma lem4353119 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353120 {A : Type'} (s' : A -> Prop) (_49722 : A) : (term151 A s' _49722) = (s' _49722).
Proof. exact (@lem4353119 (s' _49722)). Qed.
Lemma lem4353121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353122 {A : Type'} (s' : A -> Prop) (_49722 : A) : (term770 A s' _49722) = (term96 A s' _49722).
Proof. exact (MK_COMB (@lem4353121) (@lem4353120 A s' _49722)). Qed.
Lemma lem4353123 {A : Type'} (s : A -> Prop) (_49722 : A) : (s _49722) = (s _49722).
Proof. exact (eq_refl (s _49722)). Qed.
Lemma lem4353124 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49722 : A) : (term769 A s' s _49722) = (term114 A s' s _49722).
Proof. exact (MK_COMB (@lem4353122 A s' _49722) (@lem4353123 A s _49722)). Qed.
Lemma lem4353125 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49722 : A) : (term765 A s s' _49722) = (term114 A s' s _49722).
Proof. exact (TRANS (@lem4353117 A s' s _49722) (@lem4353124 A s' s _49722)). Qed.
Lemma lem4353128 {A B : Type'} (_49722 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49722.
Proof. exact (EQ_MP (@lem4353125 A s' s _49722) (@lem4353114 A B _49722 s' s t' t h1)). Qed.
Lemma lem4353129 {A B : Type'} (_49722 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s _49722.
Proof. exact (@lem4353128 A B _49722 s' s t' t h1). Qed.
Lemma lem4353130 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 A s' s x''.
Proof. exact (@lem4353129 A B x'' s' s t' t h1). Qed.
Lemma lem4353133 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (@lem4353130 A B x'' s' s t' t h1 (@lem4353085 A s' s x'' h2)). Qed.
Lemma lem4353134 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4353133 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4353136 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353137 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4353136 (s x'')). Qed.
Lemma lem4353138 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : s x''.
Proof. exact (EQ_MP (@lem4353137 A s x'') (@lem4353134 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4353141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353143 {A : Type'} (s : A -> Prop) (x'' : A) : (term99 A s x'') = (term98 A s x'').
Proof. exact (@lem4353141 (s x'')). Qed.
Lemma lem4353146 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term98 A s x''.
Proof. exact (EQ_MP (@lem4353143 A s x'') (@lem4350178 A s' s x'' h1)). Qed.
Lemma lem4353149 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (@lem4353146 A s' s x'' h2 (@lem4353138 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4353150 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4353149 A B t' t s' s x'' h1 h2). Qed.
Lemma lem4353152 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353153 : term764 = False.
Proof. exact (@lem4353152 False). Qed.
Lemma lem4353154 {A B : Type'} (t' : B -> Prop) (t : B -> Prop) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4353153) (@lem4353150 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4353156 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344277 B t t' x''' h1)). Qed.
Lemma lem4353157 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4353156 B t t' x''' h1). Qed.
Lemma lem4353159 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353160 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4353159 (t x''')). Qed.
Lemma lem4353161 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4353160 B t x''') (@lem4353157 B t t' x''' h1)). Qed.
Lemma lem4353167 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353168 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : (term163 B t t' _49729) = (term765 B t' t _49729).
Proof. exact (@lem4353167 (t' _49729) (term99 B t _49729)). Qed.
Lemma lem4353174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353175 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : (term766 B t t' _49729) = (term767 B t' t _49729).
Proof. exact (MK_COMB (@lem4353174) (@lem4353168 B t' t _49729)). Qed.
Lemma lem4353181 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : (term765 B t' t _49729) = (term765 B t' t _49729).
Proof. exact (eq_refl (term765 B t' t _49729)). Qed.
Lemma lem4353182 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : ((term163 B t t' _49729) = (term765 B t' t _49729)) = ((term765 B t' t _49729) = (term765 B t' t _49729)).
Proof. exact (MK_COMB (@lem4353175 B t' t _49729) (@lem4353181 B t' t _49729)). Qed.
Lemma lem4353184 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353185 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353184 Prop x). Qed.
Lemma lem4353186 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : ((term765 B t' t _49729) = (term765 B t' t _49729)) = True.
Proof. exact (@lem4353185 (term765 B t' t _49729)). Qed.
Lemma lem4353187 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : ((term163 B t t' _49729) = (term765 B t' t _49729)) = True.
Proof. exact (TRANS (@lem4353182 B t' t _49729) (@lem4353186 B t' t _49729)). Qed.
Lemma lem4353188 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : True = ((term163 B t t' _49729) = (term765 B t' t _49729)).
Proof. exact (SYM (@lem4353187 B t' t _49729)). Qed.
Lemma lem4353189 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49729 : B) : (term163 B t t' _49729) = (term765 B t' t _49729).
Proof. exact (EQ_MP (@lem4353188 B t' t _49729) (@lem0)). Qed.
Lemma lem4353190 {A B : Type'} (_49729 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 B t' t _49729.
Proof. exact (EQ_MP (@lem4353189 B t' t _49729) (@lem4350206 A B _49729 s s' t t' h1)). Qed.
Lemma lem4353192 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353193 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49729 : B) : (term765 B t' t _49729) = (term769 B t t' _49729).
Proof. exact (@lem4353192 (term99 B t _49729) (t' _49729)). Qed.
Lemma lem4353195 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353196 {B : Type'} (t : B -> Prop) (_49729 : B) : (term151 B t _49729) = (t _49729).
Proof. exact (@lem4353195 (t _49729)). Qed.
Lemma lem4353197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353198 {B : Type'} (t : B -> Prop) (_49729 : B) : (term770 B t _49729) = (term96 B t _49729).
Proof. exact (MK_COMB (@lem4353197) (@lem4353196 B t _49729)). Qed.
Lemma lem4353199 {B : Type'} (t' : B -> Prop) (_49729 : B) : (t' _49729) = (t' _49729).
Proof. exact (eq_refl (t' _49729)). Qed.
Lemma lem4353200 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49729 : B) : (term769 B t t' _49729) = (term114 B t t' _49729).
Proof. exact (MK_COMB (@lem4353198 B t _49729) (@lem4353199 B t' _49729)). Qed.
Lemma lem4353201 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49729 : B) : (term765 B t' t _49729) = (term114 B t t' _49729).
Proof. exact (TRANS (@lem4353193 B t t' _49729) (@lem4353200 B t t' _49729)). Qed.
Lemma lem4353204 {A B : Type'} (_49729 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49729.
Proof. exact (EQ_MP (@lem4353201 B t t' _49729) (@lem4353190 A B _49729 s s' t t' h1)). Qed.
Lemma lem4353205 {A B : Type'} (_49729 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49729.
Proof. exact (@lem4353204 A B _49729 s s' t t' h1). Qed.
Lemma lem4353206 {A B : Type'} (x''' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' x'''.
Proof. exact (@lem4353205 A B x''' s s' t t' h1). Qed.
Lemma lem4353209 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (@lem4353206 A B x''' s s' t t' h1 (@lem4353161 B t t' x''' h2)). Qed.
Lemma lem4353210 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4353209 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4353212 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353213 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4353212 (t' x''')). Qed.
Lemma lem4353214 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (EQ_MP (@lem4353213 B t' x''') (@lem4353210 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4353217 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353219 {B : Type'} (t' : B -> Prop) (x''' : B) : (term99 B t' x''') = (term98 B t' x''').
Proof. exact (@lem4353217 (t' x''')). Qed.
Lemma lem4353222 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term98 B t' x'''.
Proof. exact (EQ_MP (@lem4353219 B t' x''') (@lem4350210 B t t' x''' h1)). Qed.
Lemma lem4353225 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4353222 B t t' x''' h2 (@lem4353214 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4353226 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353225 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4353228 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353229 : term764 = False.
Proof. exact (@lem4353228 False). Qed.
Lemma lem4353230 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4353229) (@lem4353226 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4353232 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344277 B t t' x''' h1)). Qed.
Lemma lem4353233 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4353232 B t t' x''' h1). Qed.
Lemma lem4353235 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353236 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4353235 (t x''')). Qed.
Lemma lem4353237 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4353236 B t x''') (@lem4353233 B t t' x''' h1)). Qed.
Lemma lem4353243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353244 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : (term163 B t t' _49733) = (term765 B t' t _49733).
Proof. exact (@lem4353243 (t' _49733) (term99 B t _49733)). Qed.
Lemma lem4353250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353251 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : (term766 B t t' _49733) = (term767 B t' t _49733).
Proof. exact (MK_COMB (@lem4353250) (@lem4353244 B t' t _49733)). Qed.
Lemma lem4353257 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : (term765 B t' t _49733) = (term765 B t' t _49733).
Proof. exact (eq_refl (term765 B t' t _49733)). Qed.
Lemma lem4353258 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : ((term163 B t t' _49733) = (term765 B t' t _49733)) = ((term765 B t' t _49733) = (term765 B t' t _49733)).
Proof. exact (MK_COMB (@lem4353251 B t' t _49733) (@lem4353257 B t' t _49733)). Qed.
Lemma lem4353260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353261 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353260 Prop x). Qed.
Lemma lem4353262 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : ((term765 B t' t _49733) = (term765 B t' t _49733)) = True.
Proof. exact (@lem4353261 (term765 B t' t _49733)). Qed.
Lemma lem4353263 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : ((term163 B t t' _49733) = (term765 B t' t _49733)) = True.
Proof. exact (TRANS (@lem4353258 B t' t _49733) (@lem4353262 B t' t _49733)). Qed.
Lemma lem4353264 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : True = ((term163 B t t' _49733) = (term765 B t' t _49733)).
Proof. exact (SYM (@lem4353263 B t' t _49733)). Qed.
Lemma lem4353265 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49733 : B) : (term163 B t t' _49733) = (term765 B t' t _49733).
Proof. exact (EQ_MP (@lem4353264 B t' t _49733) (@lem0)). Qed.
Lemma lem4353266 {A B : Type'} (_49733 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term765 B t' t _49733.
Proof. exact (EQ_MP (@lem4353265 B t' t _49733) (@lem4350238 A B _49733 s s' t t' h1)). Qed.
Lemma lem4353268 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353269 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49733 : B) : (term765 B t' t _49733) = (term769 B t t' _49733).
Proof. exact (@lem4353268 (term99 B t _49733) (t' _49733)). Qed.
Lemma lem4353271 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353272 {B : Type'} (t : B -> Prop) (_49733 : B) : (term151 B t _49733) = (t _49733).
Proof. exact (@lem4353271 (t _49733)). Qed.
Lemma lem4353273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353274 {B : Type'} (t : B -> Prop) (_49733 : B) : (term770 B t _49733) = (term96 B t _49733).
Proof. exact (MK_COMB (@lem4353273) (@lem4353272 B t _49733)). Qed.
Lemma lem4353275 {B : Type'} (t' : B -> Prop) (_49733 : B) : (t' _49733) = (t' _49733).
Proof. exact (eq_refl (t' _49733)). Qed.
Lemma lem4353276 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49733 : B) : (term769 B t t' _49733) = (term114 B t t' _49733).
Proof. exact (MK_COMB (@lem4353274 B t _49733) (@lem4353275 B t' _49733)). Qed.
Lemma lem4353277 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49733 : B) : (term765 B t' t _49733) = (term114 B t t' _49733).
Proof. exact (TRANS (@lem4353269 B t t' _49733) (@lem4353276 B t t' _49733)). Qed.
Lemma lem4353280 {A B : Type'} (_49733 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49733.
Proof. exact (EQ_MP (@lem4353277 B t t' _49733) (@lem4353266 A B _49733 s s' t t' h1)). Qed.
Lemma lem4353281 {A B : Type'} (_49733 : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' _49733.
Proof. exact (@lem4353280 A B _49733 s s' t t' h1). Qed.
Lemma lem4353282 {A B : Type'} (x''' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s s' t t') : term114 B t t' x'''.
Proof. exact (@lem4353281 A B x''' s s' t t' h1). Qed.
Lemma lem4353285 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (@lem4353282 A B x''' s s' t t' h1 (@lem4353237 B t t' x''' h2)). Qed.
Lemma lem4353286 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4353285 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4353288 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353289 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4353288 (t' x''')). Qed.
Lemma lem4353290 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : t' x'''.
Proof. exact (EQ_MP (@lem4353289 B t' x''') (@lem4353286 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4353293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353295 {B : Type'} (t' : B -> Prop) (x''' : B) : (term99 B t' x''') = (term98 B t' x''').
Proof. exact (@lem4353293 (t' x''')). Qed.
Lemma lem4353298 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term98 B t' x'''.
Proof. exact (EQ_MP (@lem4353295 B t' x''') (@lem4350242 B t t' x''' h1)). Qed.
Lemma lem4353301 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4353298 B t t' x''' h2 (@lem4353290 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4353302 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353301 A B s s' t t' x''' h1 h2). Qed.
Lemma lem4353304 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353305 : term764 = False.
Proof. exact (@lem4353304 False). Qed.
Lemma lem4353306 {A B : Type'} (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4353305) (@lem4353302 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4353308 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344278 B t' t x''' h1)). Qed.
Lemma lem4353309 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4353308 B t' t x''' h1). Qed.
Lemma lem4353311 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353312 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4353311 (t' x''')). Qed.
Lemma lem4353313 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4353312 B t' x''') (@lem4353309 B t' t x''' h1)). Qed.
Lemma lem4353319 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353320 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : (term163 B t' t _49735) = (term765 B t t' _49735).
Proof. exact (@lem4353319 (t _49735) (term99 B t' _49735)). Qed.
Lemma lem4353326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353327 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : (term766 B t' t _49735) = (term767 B t t' _49735).
Proof. exact (MK_COMB (@lem4353326) (@lem4353320 B t t' _49735)). Qed.
Lemma lem4353333 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : (term765 B t t' _49735) = (term765 B t t' _49735).
Proof. exact (eq_refl (term765 B t t' _49735)). Qed.
Lemma lem4353334 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : ((term163 B t' t _49735) = (term765 B t t' _49735)) = ((term765 B t t' _49735) = (term765 B t t' _49735)).
Proof. exact (MK_COMB (@lem4353327 B t t' _49735) (@lem4353333 B t t' _49735)). Qed.
Lemma lem4353336 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353337 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353336 Prop x). Qed.
Lemma lem4353338 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : ((term765 B t t' _49735) = (term765 B t t' _49735)) = True.
Proof. exact (@lem4353337 (term765 B t t' _49735)). Qed.
Lemma lem4353339 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : ((term163 B t' t _49735) = (term765 B t t' _49735)) = True.
Proof. exact (TRANS (@lem4353334 B t t' _49735) (@lem4353338 B t t' _49735)). Qed.
Lemma lem4353340 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : True = ((term163 B t' t _49735) = (term765 B t t' _49735)).
Proof. exact (SYM (@lem4353339 B t t' _49735)). Qed.
Lemma lem4353341 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49735 : B) : (term163 B t' t _49735) = (term765 B t t' _49735).
Proof. exact (EQ_MP (@lem4353340 B t t' _49735) (@lem0)). Qed.
Lemma lem4353342 {A B : Type'} (_49735 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 B t t' _49735.
Proof. exact (EQ_MP (@lem4353341 B t t' _49735) (@lem4350258 A B _49735 s' s t' t h1)). Qed.
Lemma lem4353344 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353345 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49735 : B) : (term765 B t t' _49735) = (term769 B t' t _49735).
Proof. exact (@lem4353344 (term99 B t' _49735) (t _49735)). Qed.
Lemma lem4353347 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353348 {B : Type'} (t' : B -> Prop) (_49735 : B) : (term151 B t' _49735) = (t' _49735).
Proof. exact (@lem4353347 (t' _49735)). Qed.
Lemma lem4353349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353350 {B : Type'} (t' : B -> Prop) (_49735 : B) : (term770 B t' _49735) = (term96 B t' _49735).
Proof. exact (MK_COMB (@lem4353349) (@lem4353348 B t' _49735)). Qed.
Lemma lem4353351 {B : Type'} (t : B -> Prop) (_49735 : B) : (t _49735) = (t _49735).
Proof. exact (eq_refl (t _49735)). Qed.
Lemma lem4353352 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49735 : B) : (term769 B t' t _49735) = (term114 B t' t _49735).
Proof. exact (MK_COMB (@lem4353350 B t' _49735) (@lem4353351 B t _49735)). Qed.
Lemma lem4353353 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49735 : B) : (term765 B t t' _49735) = (term114 B t' t _49735).
Proof. exact (TRANS (@lem4353345 B t' t _49735) (@lem4353352 B t' t _49735)). Qed.
Lemma lem4353356 {A B : Type'} (_49735 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49735.
Proof. exact (EQ_MP (@lem4353353 B t' t _49735) (@lem4353342 A B _49735 s' s t' t h1)). Qed.
Lemma lem4353357 {A B : Type'} (_49735 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49735.
Proof. exact (@lem4353356 A B _49735 s' s t' t h1). Qed.
Lemma lem4353358 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t x'''.
Proof. exact (@lem4353357 A B x''' s' s t' t h1). Qed.
Lemma lem4353361 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (@lem4353358 A B x''' s' s t' t h1 (@lem4353313 B t' t x''' h2)). Qed.
Lemma lem4353362 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4353361 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4353364 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353365 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4353364 (t x''')). Qed.
Lemma lem4353366 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (EQ_MP (@lem4353365 B t x''') (@lem4353362 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4353369 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353371 {B : Type'} (t : B -> Prop) (x''' : B) : (term99 B t x''') = (term98 B t x''').
Proof. exact (@lem4353369 (t x''')). Qed.
Lemma lem4353374 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term98 B t x'''.
Proof. exact (EQ_MP (@lem4353371 B t x''') (@lem4350274 B t' t x''' h1)). Qed.
Lemma lem4353377 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (@lem4353374 B t' t x''' h2 (@lem4353366 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4353378 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353377 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4353380 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353381 : term764 = False.
Proof. exact (@lem4353380 False). Qed.
Lemma lem4353382 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4353381) (@lem4353378 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4353384 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344278 B t' t x''' h1)). Qed.
Lemma lem4353385 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4353384 B t' t x''' h1). Qed.
Lemma lem4353387 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353388 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4353387 (t' x''')). Qed.
Lemma lem4353389 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4353388 B t' x''') (@lem4353385 B t' t x''' h1)). Qed.
Lemma lem4353395 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353396 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : (term163 B t' t _49739) = (term765 B t t' _49739).
Proof. exact (@lem4353395 (t _49739) (term99 B t' _49739)). Qed.
Lemma lem4353402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353403 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : (term766 B t' t _49739) = (term767 B t t' _49739).
Proof. exact (MK_COMB (@lem4353402) (@lem4353396 B t t' _49739)). Qed.
Lemma lem4353409 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : (term765 B t t' _49739) = (term765 B t t' _49739).
Proof. exact (eq_refl (term765 B t t' _49739)). Qed.
Lemma lem4353410 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : ((term163 B t' t _49739) = (term765 B t t' _49739)) = ((term765 B t t' _49739) = (term765 B t t' _49739)).
Proof. exact (MK_COMB (@lem4353403 B t t' _49739) (@lem4353409 B t t' _49739)). Qed.
Lemma lem4353412 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353413 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353412 Prop x). Qed.
Lemma lem4353414 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : ((term765 B t t' _49739) = (term765 B t t' _49739)) = True.
Proof. exact (@lem4353413 (term765 B t t' _49739)). Qed.
Lemma lem4353415 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : ((term163 B t' t _49739) = (term765 B t t' _49739)) = True.
Proof. exact (TRANS (@lem4353410 B t t' _49739) (@lem4353414 B t t' _49739)). Qed.
Lemma lem4353416 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : True = ((term163 B t' t _49739) = (term765 B t t' _49739)).
Proof. exact (SYM (@lem4353415 B t t' _49739)). Qed.
Lemma lem4353417 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49739 : B) : (term163 B t' t _49739) = (term765 B t t' _49739).
Proof. exact (EQ_MP (@lem4353416 B t t' _49739) (@lem0)). Qed.
Lemma lem4353418 {A B : Type'} (_49739 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term765 B t t' _49739.
Proof. exact (EQ_MP (@lem4353417 B t t' _49739) (@lem4350290 A B _49739 s' s t' t h1)). Qed.
Lemma lem4353420 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353421 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49739 : B) : (term765 B t t' _49739) = (term769 B t' t _49739).
Proof. exact (@lem4353420 (term99 B t' _49739) (t _49739)). Qed.
Lemma lem4353423 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353424 {B : Type'} (t' : B -> Prop) (_49739 : B) : (term151 B t' _49739) = (t' _49739).
Proof. exact (@lem4353423 (t' _49739)). Qed.
Lemma lem4353425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353426 {B : Type'} (t' : B -> Prop) (_49739 : B) : (term770 B t' _49739) = (term96 B t' _49739).
Proof. exact (MK_COMB (@lem4353425) (@lem4353424 B t' _49739)). Qed.
Lemma lem4353427 {B : Type'} (t : B -> Prop) (_49739 : B) : (t _49739) = (t _49739).
Proof. exact (eq_refl (t _49739)). Qed.
Lemma lem4353428 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49739 : B) : (term769 B t' t _49739) = (term114 B t' t _49739).
Proof. exact (MK_COMB (@lem4353426 B t' _49739) (@lem4353427 B t _49739)). Qed.
Lemma lem4353429 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49739 : B) : (term765 B t t' _49739) = (term114 B t' t _49739).
Proof. exact (TRANS (@lem4353421 B t' t _49739) (@lem4353428 B t' t _49739)). Qed.
Lemma lem4353432 {A B : Type'} (_49739 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49739.
Proof. exact (EQ_MP (@lem4353429 B t' t _49739) (@lem4353418 A B _49739 s' s t' t h1)). Qed.
Lemma lem4353433 {A B : Type'} (_49739 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t _49739.
Proof. exact (@lem4353432 A B _49739 s' s t' t h1). Qed.
Lemma lem4353434 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term179 A B s' s t' t) : term114 B t' t x'''.
Proof. exact (@lem4353433 A B x''' s' s t' t h1). Qed.
Lemma lem4353437 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (@lem4353434 A B x''' s' s t' t h1 (@lem4353389 B t' t x''' h2)). Qed.
Lemma lem4353438 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4353437 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4353440 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353441 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4353440 (t x''')). Qed.
Lemma lem4353442 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : t x'''.
Proof. exact (EQ_MP (@lem4353441 B t x''') (@lem4353438 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4353445 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353447 {B : Type'} (t : B -> Prop) (x''' : B) : (term99 B t x''') = (term98 B t x''').
Proof. exact (@lem4353445 (t x''')). Qed.
Lemma lem4353450 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term98 B t x'''.
Proof. exact (EQ_MP (@lem4353447 B t x''') (@lem4350306 B t' t x''' h1)). Qed.
Lemma lem4353453 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (@lem4353450 B t' t x''' h2 (@lem4353442 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4353454 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353453 A B s' s t' t x''' h1 h2). Qed.
Lemma lem4353456 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353457 : term764 = False.
Proof. exact (@lem4353456 False). Qed.
Lemma lem4353458 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4353457) (@lem4353454 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4353460 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344311 A s s' x'' h1)). Qed.
Lemma lem4353461 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4353460 A s s' x'' h1). Qed.
Lemma lem4353463 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353464 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4353463 (s x'')). Qed.
Lemma lem4353465 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4353464 A s x'') (@lem4353461 A s s' x'' h1)). Qed.
Lemma lem4353468 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353470 {A : Type'} (s : A -> Prop) (_49743 : A) : (term99 A s _49743) = (term98 A s _49743).
Proof. exact (@lem4353468 (s _49743)). Qed.
Lemma lem4353473 {A : Type'} (_49743 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49743.
Proof. exact (EQ_MP (@lem4353470 A s _49743) (@lem4350314 A _49743 s h1)). Qed.
Lemma lem4353474 {A : Type'} (_49743 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49743.
Proof. exact (@lem4353473 A _49743 s h1). Qed.
Lemma lem4353475 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x''.
Proof. exact (@lem4353474 A x'' s h1). Qed.
Lemma lem4353478 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4353475 A x'' s h1 (@lem4353465 A s s' x'' h2)). Qed.
Lemma lem4353479 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4353478 A s s' x'' h1 h2). Qed.
Lemma lem4353481 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353482 : term764 = False.
Proof. exact (@lem4353481 False). Qed.
Lemma lem4353483 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4353482) (@lem4353479 A s s' x'' h1 h2)). Qed.
Lemma lem4353485 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : s x.
Proof. exact (proj1 (@lem4344305 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353486 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4353485 A B x x' s s' x'' t t' x''' h1). Qed.
Lemma lem4353488 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353489 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4353488 (s x)). Qed.
Lemma lem4353490 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : s x.
Proof. exact (EQ_MP (@lem4353489 A s x) (@lem4353486 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353493 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353495 {A : Type'} (s : A -> Prop) (_49745 : A) : (term99 A s _49745) = (term98 A s _49745).
Proof. exact (@lem4353493 (s _49745)). Qed.
Lemma lem4353498 {A : Type'} (_49745 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49745.
Proof. exact (EQ_MP (@lem4353495 A s _49745) (@lem4350326 A _49745 s h1)). Qed.
Lemma lem4353499 {A : Type'} (_49745 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49745.
Proof. exact (@lem4353498 A _49745 s h1). Qed.
Lemma lem4353500 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4353499 A x s h1). Qed.
Lemma lem4353503 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (@lem4353500 A x s h1 (@lem4353490 A B x x' s s' x'' t t' x''' h2)). Qed.
Lemma lem4353504 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353503 A B x x' s s' x'' t t' x''' h1 h2). Qed.
Lemma lem4353506 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353507 : term764 = False.
Proof. exact (@lem4353506 False). Qed.
Lemma lem4353508 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4353507) (@lem4353504 A B x x' s s' x'' t t' x''' h1 h2)). Qed.
Lemma lem4353510 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344321 A s' s x'' h1)). Qed.
Lemma lem4353511 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4353510 A s' s x'' h1). Qed.
Lemma lem4353513 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353514 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4353513 (s' x'')). Qed.
Lemma lem4353515 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4353514 A s' x'') (@lem4353511 A s' s x'' h1)). Qed.
Lemma lem4353518 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353520 {A : Type'} (s' : A -> Prop) (_49746 : A) : (term99 A s' _49746) = (term98 A s' _49746).
Proof. exact (@lem4353518 (s' _49746)). Qed.
Lemma lem4353523 {A : Type'} (_49746 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49746.
Proof. exact (EQ_MP (@lem4353520 A s' _49746) (@lem4350336 A _49746 s' h1)). Qed.
Lemma lem4353524 {A : Type'} (_49746 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49746.
Proof. exact (@lem4353523 A _49746 s' h1). Qed.
Lemma lem4353525 {A : Type'} (x'' : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x''.
Proof. exact (@lem4353524 A x'' s' h1). Qed.
Lemma lem4353528 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (@lem4353525 A x'' s' h1 (@lem4353515 A s' s x'' h2)). Qed.
Lemma lem4353529 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4353528 A s' s x'' h1 h2). Qed.
Lemma lem4353531 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353532 : term764 = False.
Proof. exact (@lem4353531 False). Qed.
Lemma lem4353533 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4353532) (@lem4353529 A s' s x'' h1 h2)). Qed.
Lemma lem4353535 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : s' x.
Proof. exact (proj1 (@lem4344306 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353536 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4353535 A B x x' s' s x'' t' t x''' h1). Qed.
Lemma lem4353538 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353539 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4353538 (s' x)). Qed.
Lemma lem4353540 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : s' x.
Proof. exact (EQ_MP (@lem4353539 A s' x) (@lem4353536 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353543 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353545 {A : Type'} (s' : A -> Prop) (_49748 : A) : (term99 A s' _49748) = (term98 A s' _49748).
Proof. exact (@lem4353543 (s' _49748)). Qed.
Lemma lem4353548 {A : Type'} (_49748 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49748.
Proof. exact (EQ_MP (@lem4353545 A s' _49748) (@lem4350348 A _49748 s' h1)). Qed.
Lemma lem4353549 {A : Type'} (_49748 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49748.
Proof. exact (@lem4353548 A _49748 s' h1). Qed.
Lemma lem4353550 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4353549 A x s' h1). Qed.
Lemma lem4353553 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (@lem4353550 A x s' h1 (@lem4353540 A B x x' s' s x'' t' t x''' h2)). Qed.
Lemma lem4353554 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353553 A B x x' s' s x'' t' t x''' h1 h2). Qed.
Lemma lem4353556 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353557 : term764 = False.
Proof. exact (@lem4353556 False). Qed.
Lemma lem4353558 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4353557) (@lem4353554 A B x x' s' s x'' t' t x''' h1 h2)). Qed.
Lemma lem4353560 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : t x'.
Proof. exact (proj1 (@lem4344329 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353561 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4353560 A B x x' s s' x'' t t' x''' h1). Qed.
Lemma lem4353563 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353564 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4353563 (t x')). Qed.
Lemma lem4353565 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : t x'.
Proof. exact (EQ_MP (@lem4353564 B t x') (@lem4353561 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353568 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353570 {B : Type'} (t : B -> Prop) (_49751 : B) : (term99 B t _49751) = (term98 B t _49751).
Proof. exact (@lem4353568 (t _49751)). Qed.
Lemma lem4353573 {B : Type'} (_49751 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49751.
Proof. exact (EQ_MP (@lem4353570 B t _49751) (@lem4350362 B _49751 t h1)). Qed.
Lemma lem4353574 {B : Type'} (_49751 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49751.
Proof. exact (@lem4353573 B _49751 t h1). Qed.
Lemma lem4353575 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4353574 B x' t h1). Qed.
Lemma lem4353578 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (@lem4353575 B x' t h1 (@lem4353565 A B x x' s s' x'' t t' x''' h2)). Qed.
Lemma lem4353579 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353578 A B x x' s s' x'' t t' x''' h1 h2). Qed.
Lemma lem4353581 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353582 : term764 = False.
Proof. exact (@lem4353581 False). Qed.
Lemma lem4353583 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4353582) (@lem4353579 A B x x' s s' x'' t t' x''' h1 h2)). Qed.
Lemma lem4353585 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344334 B t t' x''' h1)). Qed.
Lemma lem4353586 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4353585 B t t' x''' h1). Qed.
Lemma lem4353588 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353589 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4353588 (t x''')). Qed.
Lemma lem4353590 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4353589 B t x''') (@lem4353586 B t t' x''' h1)). Qed.
Lemma lem4353593 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353595 {B : Type'} (t : B -> Prop) (_49753 : B) : (term99 B t _49753) = (term98 B t _49753).
Proof. exact (@lem4353593 (t _49753)). Qed.
Lemma lem4353598 {B : Type'} (_49753 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49753.
Proof. exact (EQ_MP (@lem4353595 B t _49753) (@lem4350374 B _49753 t h1)). Qed.
Lemma lem4353599 {B : Type'} (_49753 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49753.
Proof. exact (@lem4353598 B _49753 t h1). Qed.
Lemma lem4353600 {B : Type'} (x''' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'''.
Proof. exact (@lem4353599 B x''' t h1). Qed.
Lemma lem4353603 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4353600 B x''' t h1 (@lem4353590 B t t' x''' h2)). Qed.
Lemma lem4353604 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353603 B t t' x''' h1 h2). Qed.
Lemma lem4353606 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353607 : term764 = False.
Proof. exact (@lem4353606 False). Qed.
Lemma lem4353608 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4353607) (@lem4353604 B t t' x''' h1 h2)). Qed.
Lemma lem4353610 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344343 A s' s x'' h1)). Qed.
Lemma lem4353611 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4353610 A s' s x'' h1). Qed.
Lemma lem4353613 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353614 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4353613 (s' x'')). Qed.
Lemma lem4353615 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4353614 A s' x'') (@lem4353611 A s' s x'' h1)). Qed.
Lemma lem4353618 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353620 {A : Type'} (s' : A -> Prop) (_49754 : A) : (term99 A s' _49754) = (term98 A s' _49754).
Proof. exact (@lem4353618 (s' _49754)). Qed.
Lemma lem4353623 {A : Type'} (_49754 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49754.
Proof. exact (EQ_MP (@lem4353620 A s' _49754) (@lem4350384 A _49754 s' h1)). Qed.
Lemma lem4353624 {A : Type'} (_49754 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49754.
Proof. exact (@lem4353623 A _49754 s' h1). Qed.
Lemma lem4353625 {A : Type'} (x'' : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x''.
Proof. exact (@lem4353624 A x'' s' h1). Qed.
Lemma lem4353628 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (@lem4353625 A x'' s' h1 (@lem4353615 A s' s x'' h2)). Qed.
Lemma lem4353629 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4353628 A s' s x'' h1 h2). Qed.
Lemma lem4353631 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353632 : term764 = False.
Proof. exact (@lem4353631 False). Qed.
Lemma lem4353633 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4353632) (@lem4353629 A s' s x'' h1 h2)). Qed.
Lemma lem4353635 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : s' x.
Proof. exact (proj1 (@lem4344328 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353636 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term762 A s' x.
Proof. exact (fun h0 : term99 A s' x => @lem4353635 A B x x' s' s x'' t' t x''' h1). Qed.
Lemma lem4353638 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353639 {A : Type'} (s' : A -> Prop) (x : A) : (term762 A s' x) = (s' x).
Proof. exact (@lem4353638 (s' x)). Qed.
Lemma lem4353640 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : s' x.
Proof. exact (EQ_MP (@lem4353639 A s' x) (@lem4353636 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353643 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353645 {A : Type'} (s' : A -> Prop) (_49756 : A) : (term99 A s' _49756) = (term98 A s' _49756).
Proof. exact (@lem4353643 (s' _49756)). Qed.
Lemma lem4353648 {A : Type'} (_49756 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49756.
Proof. exact (EQ_MP (@lem4353645 A s' _49756) (@lem4350396 A _49756 s' h1)). Qed.
Lemma lem4353649 {A : Type'} (_49756 : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' _49756.
Proof. exact (@lem4353648 A _49756 s' h1). Qed.
Lemma lem4353650 {A : Type'} (x : A) (s' : A -> Prop) (h1 : term102 A s') : term98 A s' x.
Proof. exact (@lem4353649 A x s' h1). Qed.
Lemma lem4353653 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (@lem4353650 A x s' h1 (@lem4353640 A B x x' s' s x'' t' t x''' h2)). Qed.
Lemma lem4353654 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353653 A B x x' s' s x'' t' t x''' h1 h2). Qed.
Lemma lem4353656 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353657 : term764 = False.
Proof. exact (@lem4353656 False). Qed.
Lemma lem4353658 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4353657) (@lem4353654 A B x x' s' s x'' t' t x''' h1 h2)). Qed.
Lemma lem4353660 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344357 A s s' x'' h1)). Qed.
Lemma lem4353661 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4353660 A s s' x'' h1). Qed.
Lemma lem4353663 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353664 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4353663 (s x'')). Qed.
Lemma lem4353665 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4353664 A s x'') (@lem4353661 A s s' x'' h1)). Qed.
Lemma lem4353668 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353670 {A : Type'} (s : A -> Prop) (_49759 : A) : (term99 A s _49759) = (term98 A s _49759).
Proof. exact (@lem4353668 (s _49759)). Qed.
Lemma lem4353673 {A : Type'} (_49759 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49759.
Proof. exact (EQ_MP (@lem4353670 A s _49759) (@lem4350410 A _49759 s h1)). Qed.
Lemma lem4353674 {A : Type'} (_49759 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49759.
Proof. exact (@lem4353673 A _49759 s h1). Qed.
Lemma lem4353675 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x''.
Proof. exact (@lem4353674 A x'' s h1). Qed.
Lemma lem4353678 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (@lem4353675 A x'' s h1 (@lem4353665 A s s' x'' h2)). Qed.
Lemma lem4353679 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : term764.
Proof. exact (fun h0 : ~ False => @lem4353678 A s s' x'' h1 h2). Qed.
Lemma lem4353681 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353682 : term764 = False.
Proof. exact (@lem4353681 False). Qed.
Lemma lem4353683 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4353682) (@lem4353679 A s s' x'' h1 h2)). Qed.
Lemma lem4353685 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : s x.
Proof. exact (proj1 (@lem4344351 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353686 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term762 A s x.
Proof. exact (fun h0 : term99 A s x => @lem4353685 A B x x' s s' x'' t t' x''' h1). Qed.
Lemma lem4353688 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353689 {A : Type'} (s : A -> Prop) (x : A) : (term762 A s x) = (s x).
Proof. exact (@lem4353688 (s x)). Qed.
Lemma lem4353690 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : s x.
Proof. exact (EQ_MP (@lem4353689 A s x) (@lem4353686 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353693 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353695 {A : Type'} (s : A -> Prop) (_49761 : A) : (term99 A s _49761) = (term98 A s _49761).
Proof. exact (@lem4353693 (s _49761)). Qed.
Lemma lem4353698 {A : Type'} (_49761 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49761.
Proof. exact (EQ_MP (@lem4353695 A s _49761) (@lem4350422 A _49761 s h1)). Qed.
Lemma lem4353699 {A : Type'} (_49761 : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s _49761.
Proof. exact (@lem4353698 A _49761 s h1). Qed.
Lemma lem4353700 {A : Type'} (x : A) (s : A -> Prop) (h1 : term102 A s) : term98 A s x.
Proof. exact (@lem4353699 A x s h1). Qed.
Lemma lem4353703 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (@lem4353700 A x s h1 (@lem4353690 A B x x' s s' x'' t t' x''' h2)). Qed.
Lemma lem4353704 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353703 A B x x' s s' x'' t t' x''' h1 h2). Qed.
Lemma lem4353706 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353707 : term764 = False.
Proof. exact (@lem4353706 False). Qed.
Lemma lem4353708 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4353707) (@lem4353704 A B x x' s s' x'' t t' x''' h1 h2)). Qed.
Lemma lem4353710 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : t' x'.
Proof. exact (proj1 (@lem4344363 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353711 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4353710 A B x x' s' s x'' t' t x''' h1). Qed.
Lemma lem4353713 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353714 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4353713 (t' x')). Qed.
Lemma lem4353715 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : t' x'.
Proof. exact (EQ_MP (@lem4353714 B t' x') (@lem4353711 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353718 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353720 {B : Type'} (t' : B -> Prop) (_49762 : B) : (term99 B t' _49762) = (term98 B t' _49762).
Proof. exact (@lem4353718 (t' _49762)). Qed.
Lemma lem4353723 {B : Type'} (_49762 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49762.
Proof. exact (EQ_MP (@lem4353720 B t' _49762) (@lem4350432 B _49762 t' h1)). Qed.
Lemma lem4353724 {B : Type'} (_49762 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49762.
Proof. exact (@lem4353723 B _49762 t' h1). Qed.
Lemma lem4353725 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4353724 B x' t' h1). Qed.
Lemma lem4353728 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (@lem4353725 B x' t' h1 (@lem4353715 A B x x' s' s x'' t' t x''' h2)). Qed.
Lemma lem4353729 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353728 A B x x' s' s x'' t' t x''' h1 h2). Qed.
Lemma lem4353731 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353732 : term764 = False.
Proof. exact (@lem4353731 False). Qed.
Lemma lem4353733 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4353732) (@lem4353729 A B x x' s' s x'' t' t x''' h1 h2)). Qed.
Lemma lem4353735 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344368 B t' t x''' h1)). Qed.
Lemma lem4353736 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4353735 B t' t x''' h1). Qed.
Lemma lem4353738 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353739 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4353738 (t' x''')). Qed.
Lemma lem4353740 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4353739 B t' x''') (@lem4353736 B t' t x''' h1)). Qed.
Lemma lem4353743 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353745 {B : Type'} (t' : B -> Prop) (_49764 : B) : (term99 B t' _49764) = (term98 B t' _49764).
Proof. exact (@lem4353743 (t' _49764)). Qed.
Lemma lem4353748 {B : Type'} (_49764 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49764.
Proof. exact (EQ_MP (@lem4353745 B t' _49764) (@lem4350444 B _49764 t' h1)). Qed.
Lemma lem4353749 {B : Type'} (_49764 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49764.
Proof. exact (@lem4353748 B _49764 t' h1). Qed.
Lemma lem4353750 {B : Type'} (x''' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'''.
Proof. exact (@lem4353749 B x''' t' h1). Qed.
Lemma lem4353753 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (@lem4353750 B x''' t' h1 (@lem4353740 B t' t x''' h2)). Qed.
Lemma lem4353754 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353753 B t' t x''' h1 h2). Qed.
Lemma lem4353756 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353757 : term764 = False.
Proof. exact (@lem4353756 False). Qed.
Lemma lem4353758 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4353757) (@lem4353754 B t' t x''' h1 h2)). Qed.
Lemma lem4353760 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : t x'.
Proof. exact (proj1 (@lem4344375 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353761 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : term762 B t x'.
Proof. exact (fun h0 : term99 B t x' => @lem4353760 A B x x' s s' x'' t t' x''' h1). Qed.
Lemma lem4353763 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353764 {B : Type'} (t : B -> Prop) (x' : B) : (term762 B t x') = (t x').
Proof. exact (@lem4353763 (t x')). Qed.
Lemma lem4353765 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term535 A B x x' s s' x'' t t' x''') : t x'.
Proof. exact (EQ_MP (@lem4353764 B t x') (@lem4353761 A B x x' s s' x'' t t' x''' h1)). Qed.
Lemma lem4353768 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353770 {B : Type'} (t : B -> Prop) (_49767 : B) : (term99 B t _49767) = (term98 B t _49767).
Proof. exact (@lem4353768 (t _49767)). Qed.
Lemma lem4353773 {B : Type'} (_49767 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49767.
Proof. exact (EQ_MP (@lem4353770 B t _49767) (@lem4350458 B _49767 t h1)). Qed.
Lemma lem4353774 {B : Type'} (_49767 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49767.
Proof. exact (@lem4353773 B _49767 t h1). Qed.
Lemma lem4353775 {B : Type'} (x' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'.
Proof. exact (@lem4353774 B x' t h1). Qed.
Lemma lem4353778 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (@lem4353775 B x' t h1 (@lem4353765 A B x x' s s' x'' t t' x''' h2)). Qed.
Lemma lem4353779 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353778 A B x x' s s' x'' t t' x''' h1 h2). Qed.
Lemma lem4353781 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353782 : term764 = False.
Proof. exact (@lem4353781 False). Qed.
Lemma lem4353783 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4353782) (@lem4353779 A B x x' s s' x'' t t' x''' h1 h2)). Qed.
Lemma lem4353785 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344380 B t t' x''' h1)). Qed.
Lemma lem4353786 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4353785 B t t' x''' h1). Qed.
Lemma lem4353788 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353789 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4353788 (t x''')). Qed.
Lemma lem4353790 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4353789 B t x''') (@lem4353786 B t t' x''' h1)). Qed.
Lemma lem4353793 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353795 {B : Type'} (t : B -> Prop) (_49769 : B) : (term99 B t _49769) = (term98 B t _49769).
Proof. exact (@lem4353793 (t _49769)). Qed.
Lemma lem4353798 {B : Type'} (_49769 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49769.
Proof. exact (EQ_MP (@lem4353795 B t _49769) (@lem4350470 B _49769 t h1)). Qed.
Lemma lem4353799 {B : Type'} (_49769 : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t _49769.
Proof. exact (@lem4353798 B _49769 t h1). Qed.
Lemma lem4353800 {B : Type'} (x''' : B) (t : B -> Prop) (h1 : term102 B t) : term98 B t x'''.
Proof. exact (@lem4353799 B x''' t h1). Qed.
Lemma lem4353803 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (@lem4353800 B x''' t h1 (@lem4353790 B t t' x''' h2)). Qed.
Lemma lem4353804 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353803 B t t' x''' h1 h2). Qed.
Lemma lem4353806 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353807 : term764 = False.
Proof. exact (@lem4353806 False). Qed.
Lemma lem4353808 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4353807) (@lem4353804 B t t' x''' h1 h2)). Qed.
Lemma lem4353810 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : t' x'.
Proof. exact (proj1 (@lem4344385 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353811 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : term762 B t' x'.
Proof. exact (fun h0 : term99 B t' x' => @lem4353810 A B x x' s' s x'' t' t x''' h1). Qed.
Lemma lem4353813 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353814 {B : Type'} (t' : B -> Prop) (x' : B) : (term762 B t' x') = (t' x').
Proof. exact (@lem4353813 (t' x')). Qed.
Lemma lem4353815 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term535 A B x x' s' s x'' t' t x''') : t' x'.
Proof. exact (EQ_MP (@lem4353814 B t' x') (@lem4353811 A B x x' s' s x'' t' t x''' h1)). Qed.
Lemma lem4353818 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353820 {B : Type'} (t' : B -> Prop) (_49770 : B) : (term99 B t' _49770) = (term98 B t' _49770).
Proof. exact (@lem4353818 (t' _49770)). Qed.
Lemma lem4353823 {B : Type'} (_49770 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49770.
Proof. exact (EQ_MP (@lem4353820 B t' _49770) (@lem4350480 B _49770 t' h1)). Qed.
Lemma lem4353824 {B : Type'} (_49770 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49770.
Proof. exact (@lem4353823 B _49770 t' h1). Qed.
Lemma lem4353825 {B : Type'} (x' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'.
Proof. exact (@lem4353824 B x' t' h1). Qed.
Lemma lem4353828 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (@lem4353825 B x' t' h1 (@lem4353815 A B x x' s' s x'' t' t x''' h2)). Qed.
Lemma lem4353829 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353828 A B x x' s' s x'' t' t x''' h1 h2). Qed.
Lemma lem4353831 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353832 : term764 = False.
Proof. exact (@lem4353831 False). Qed.
Lemma lem4353833 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4353832) (@lem4353829 A B x x' s' s x'' t' t x''' h1 h2)). Qed.
Lemma lem4353835 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344390 B t' t x''' h1)). Qed.
Lemma lem4353836 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4353835 B t' t x''' h1). Qed.
Lemma lem4353838 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353839 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4353838 (t' x''')). Qed.
Lemma lem4353840 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4353839 B t' x''') (@lem4353836 B t' t x''' h1)). Qed.
Lemma lem4353843 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353845 {B : Type'} (t' : B -> Prop) (_49772 : B) : (term99 B t' _49772) = (term98 B t' _49772).
Proof. exact (@lem4353843 (t' _49772)). Qed.
Lemma lem4353848 {B : Type'} (_49772 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49772.
Proof. exact (EQ_MP (@lem4353845 B t' _49772) (@lem4350492 B _49772 t' h1)). Qed.
Lemma lem4353849 {B : Type'} (_49772 : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' _49772.
Proof. exact (@lem4353848 B _49772 t' h1). Qed.
Lemma lem4353850 {B : Type'} (x''' : B) (t' : B -> Prop) (h1 : term102 B t') : term98 B t' x'''.
Proof. exact (@lem4353849 B x''' t' h1). Qed.
Lemma lem4353853 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (@lem4353850 B x''' t' h1 (@lem4353840 B t' t x''' h2)). Qed.
Lemma lem4353854 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : term764.
Proof. exact (fun h0 : ~ False => @lem4353853 B t' t x''' h1 h2). Qed.
Lemma lem4353856 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353857 : term764 = False.
Proof. exact (@lem4353856 False). Qed.
Lemma lem4353858 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4353857) (@lem4353854 B t' t x''' h1 h2)). Qed.
Lemma lem4353860 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (proj1 (@lem4344407 A s s' x'' h1)). Qed.
Lemma lem4353861 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4353860 A s s' x'' h1). Qed.
Lemma lem4353863 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353864 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4353863 (s x'')). Qed.
Lemma lem4353865 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : s x''.
Proof. exact (EQ_MP (@lem4353864 A s x'') (@lem4353861 A s s' x'' h1)). Qed.
Lemma lem4353871 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353872 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : (term163 A s s' _49776) = (term765 A s' s _49776).
Proof. exact (@lem4353871 (s' _49776) (term99 A s _49776)). Qed.
Lemma lem4353878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353879 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : (term766 A s s' _49776) = (term767 A s' s _49776).
Proof. exact (MK_COMB (@lem4353878) (@lem4353872 A s' s _49776)). Qed.
Lemma lem4353885 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : (term765 A s' s _49776) = (term765 A s' s _49776).
Proof. exact (eq_refl (term765 A s' s _49776)). Qed.
Lemma lem4353886 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : ((term163 A s s' _49776) = (term765 A s' s _49776)) = ((term765 A s' s _49776) = (term765 A s' s _49776)).
Proof. exact (MK_COMB (@lem4353879 A s' s _49776) (@lem4353885 A s' s _49776)). Qed.
Lemma lem4353888 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353889 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353888 Prop x). Qed.
Lemma lem4353890 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : ((term765 A s' s _49776) = (term765 A s' s _49776)) = True.
Proof. exact (@lem4353889 (term765 A s' s _49776)). Qed.
Lemma lem4353891 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : ((term163 A s s' _49776) = (term765 A s' s _49776)) = True.
Proof. exact (TRANS (@lem4353886 A s' s _49776) (@lem4353890 A s' s _49776)). Qed.
Lemma lem4353892 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : True = ((term163 A s s' _49776) = (term765 A s' s _49776)).
Proof. exact (SYM (@lem4353891 A s' s _49776)). Qed.
Lemma lem4353893 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49776 : A) : (term163 A s s' _49776) = (term765 A s' s _49776).
Proof. exact (EQ_MP (@lem4353892 A s' s _49776) (@lem0)). Qed.
Lemma lem4353894 {A B : Type'} (_49776 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term765 A s' s _49776.
Proof. exact (EQ_MP (@lem4353893 A s' s _49776) (@lem4350520 A B _49776 s' s t' t h1)). Qed.
Lemma lem4353896 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353897 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49776 : A) : (term765 A s' s _49776) = (term769 A s s' _49776).
Proof. exact (@lem4353896 (term99 A s _49776) (s' _49776)). Qed.
Lemma lem4353899 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353900 {A : Type'} (s : A -> Prop) (_49776 : A) : (term151 A s _49776) = (s _49776).
Proof. exact (@lem4353899 (s _49776)). Qed.
Lemma lem4353901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353902 {A : Type'} (s : A -> Prop) (_49776 : A) : (term770 A s _49776) = (term96 A s _49776).
Proof. exact (MK_COMB (@lem4353901) (@lem4353900 A s _49776)). Qed.
Lemma lem4353903 {A : Type'} (s' : A -> Prop) (_49776 : A) : (s' _49776) = (s' _49776).
Proof. exact (eq_refl (s' _49776)). Qed.
Lemma lem4353904 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49776 : A) : (term769 A s s' _49776) = (term114 A s s' _49776).
Proof. exact (MK_COMB (@lem4353902 A s _49776) (@lem4353903 A s' _49776)). Qed.
Lemma lem4353905 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49776 : A) : (term765 A s' s _49776) = (term114 A s s' _49776).
Proof. exact (TRANS (@lem4353897 A s s' _49776) (@lem4353904 A s s' _49776)). Qed.
Lemma lem4353908 {A B : Type'} (_49776 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 A s s' _49776.
Proof. exact (EQ_MP (@lem4353905 A s s' _49776) (@lem4353894 A B _49776 s' s t' t h1)). Qed.
Lemma lem4353909 {A B : Type'} (_49776 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 A s s' _49776.
Proof. exact (@lem4353908 A B _49776 s' s t' t h1). Qed.
Lemma lem4353910 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 A s s' x''.
Proof. exact (@lem4353909 A B x'' s' s t' t h1). Qed.
Lemma lem4353913 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s s' x'') (h2 : term215 A B s' s t' t) : s' x''.
Proof. exact (@lem4353910 A B x'' s' s t' t h2 (@lem4353865 A s s' x'' h1)). Qed.
Lemma lem4353914 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s s' x'') (h2 : term215 A B s' s t' t) : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4353913 A B x'' s' s t' t h1 h2). Qed.
Lemma lem4353916 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353917 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4353916 (s' x'')). Qed.
Lemma lem4353918 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s s' x'') (h2 : term215 A B s' s t' t) : s' x''.
Proof. exact (EQ_MP (@lem4353917 A s' x'') (@lem4353914 A B x'' s' s t' t h1 h2)). Qed.
Lemma lem4353921 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353923 {A : Type'} (s' : A -> Prop) (x'' : A) : (term99 A s' x'') = (term98 A s' x'').
Proof. exact (@lem4353921 (s' x'')). Qed.
Lemma lem4353926 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term162 A s s' x'') : term98 A s' x''.
Proof. exact (EQ_MP (@lem4353923 A s' x'') (@lem4350534 A s s' x'' h1)). Qed.
Lemma lem4353929 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s s' x'') (h2 : term215 A B s' s t' t) : False.
Proof. exact (@lem4353926 A s s' x'' h1 (@lem4353918 A B x'' s' s t' t h1 h2)). Qed.
Lemma lem4353930 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s s' x'') (h2 : term215 A B s' s t' t) : term764.
Proof. exact (fun h0 : ~ False => @lem4353929 A B x'' s' s t' t h1 h2). Qed.
Lemma lem4353932 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353933 : term764 = False.
Proof. exact (@lem4353932 False). Qed.
Lemma lem4353934 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s s' x'') (h2 : term215 A B s' s t' t) : False.
Proof. exact (EQ_MP (@lem4353933) (@lem4353930 A B x'' s' s t' t h1 h2)). Qed.
Lemma lem4353936 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (proj1 (@lem4344408 B t t' x''' h1)). Qed.
Lemma lem4353937 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4353936 B t t' x''' h1). Qed.
Lemma lem4353939 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353940 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4353939 (t x''')). Qed.
Lemma lem4353941 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : t x'''.
Proof. exact (EQ_MP (@lem4353940 B t x''') (@lem4353937 B t t' x''' h1)). Qed.
Lemma lem4353947 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4353948 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : (term163 B t t' _49778) = (term765 B t' t _49778).
Proof. exact (@lem4353947 (t' _49778) (term99 B t _49778)). Qed.
Lemma lem4353954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4353955 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : (term766 B t t' _49778) = (term767 B t' t _49778).
Proof. exact (MK_COMB (@lem4353954) (@lem4353948 B t' t _49778)). Qed.
Lemma lem4353961 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : (term765 B t' t _49778) = (term765 B t' t _49778).
Proof. exact (eq_refl (term765 B t' t _49778)). Qed.
Lemma lem4353962 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : ((term163 B t t' _49778) = (term765 B t' t _49778)) = ((term765 B t' t _49778) = (term765 B t' t _49778)).
Proof. exact (MK_COMB (@lem4353955 B t' t _49778) (@lem4353961 B t' t _49778)). Qed.
Lemma lem4353964 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4353965 (x : Prop) : (x = x) = True.
Proof. exact (@lem4353964 Prop x). Qed.
Lemma lem4353966 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : ((term765 B t' t _49778) = (term765 B t' t _49778)) = True.
Proof. exact (@lem4353965 (term765 B t' t _49778)). Qed.
Lemma lem4353967 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : ((term163 B t t' _49778) = (term765 B t' t _49778)) = True.
Proof. exact (TRANS (@lem4353962 B t' t _49778) (@lem4353966 B t' t _49778)). Qed.
Lemma lem4353968 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : True = ((term163 B t t' _49778) = (term765 B t' t _49778)).
Proof. exact (SYM (@lem4353967 B t' t _49778)). Qed.
Lemma lem4353969 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49778 : B) : (term163 B t t' _49778) = (term765 B t' t _49778).
Proof. exact (EQ_MP (@lem4353968 B t' t _49778) (@lem0)). Qed.
Lemma lem4353970 {A B : Type'} (_49778 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term765 B t' t _49778.
Proof. exact (EQ_MP (@lem4353969 B t' t _49778) (@lem4350540 A B _49778 s' s t' t h1)). Qed.
Lemma lem4353972 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4353973 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49778 : B) : (term765 B t' t _49778) = (term769 B t t' _49778).
Proof. exact (@lem4353972 (term99 B t _49778) (t' _49778)). Qed.
Lemma lem4353975 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4353976 {B : Type'} (t : B -> Prop) (_49778 : B) : (term151 B t _49778) = (t _49778).
Proof. exact (@lem4353975 (t _49778)). Qed.
Lemma lem4353977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4353978 {B : Type'} (t : B -> Prop) (_49778 : B) : (term770 B t _49778) = (term96 B t _49778).
Proof. exact (MK_COMB (@lem4353977) (@lem4353976 B t _49778)). Qed.
Lemma lem4353979 {B : Type'} (t' : B -> Prop) (_49778 : B) : (t' _49778) = (t' _49778).
Proof. exact (eq_refl (t' _49778)). Qed.
Lemma lem4353980 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49778 : B) : (term769 B t t' _49778) = (term114 B t t' _49778).
Proof. exact (MK_COMB (@lem4353978 B t _49778) (@lem4353979 B t' _49778)). Qed.
Lemma lem4353981 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49778 : B) : (term765 B t' t _49778) = (term114 B t t' _49778).
Proof. exact (TRANS (@lem4353973 B t t' _49778) (@lem4353980 B t t' _49778)). Qed.
Lemma lem4353984 {A B : Type'} (_49778 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 B t t' _49778.
Proof. exact (EQ_MP (@lem4353981 B t t' _49778) (@lem4353970 A B _49778 s' s t' t h1)). Qed.
Lemma lem4353985 {A B : Type'} (_49778 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 B t t' _49778.
Proof. exact (@lem4353984 A B _49778 s' s t' t h1). Qed.
Lemma lem4353986 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 B t t' x'''.
Proof. exact (@lem4353985 A B x''' s' s t' t h1). Qed.
Lemma lem4353989 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t t' x''') (h2 : term215 A B s' s t' t) : t' x'''.
Proof. exact (@lem4353986 A B x''' s' s t' t h2 (@lem4353941 B t t' x''' h1)). Qed.
Lemma lem4353990 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t t' x''') (h2 : term215 A B s' s t' t) : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4353989 A B x''' s' s t' t h1 h2). Qed.
Lemma lem4353992 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4353993 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4353992 (t' x''')). Qed.
Lemma lem4353994 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t t' x''') (h2 : term215 A B s' s t' t) : t' x'''.
Proof. exact (EQ_MP (@lem4353993 B t' x''') (@lem4353990 A B x''' s' s t' t h1 h2)). Qed.
Lemma lem4353997 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4353999 {B : Type'} (t' : B -> Prop) (x''' : B) : (term99 B t' x''') = (term98 B t' x''').
Proof. exact (@lem4353997 (t' x''')). Qed.
Lemma lem4354002 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term162 B t t' x''') : term98 B t' x'''.
Proof. exact (EQ_MP (@lem4353999 B t' x''') (@lem4350566 B t t' x''' h1)). Qed.
Lemma lem4354005 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t t' x''') (h2 : term215 A B s' s t' t) : False.
Proof. exact (@lem4354002 B t t' x''' h1 (@lem4353994 A B x''' s' s t' t h1 h2)). Qed.
Lemma lem4354006 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t t' x''') (h2 : term215 A B s' s t' t) : term764.
Proof. exact (fun h0 : ~ False => @lem4354005 A B x''' s' s t' t h1 h2). Qed.
Lemma lem4354008 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4354009 : term764 = False.
Proof. exact (@lem4354008 False). Qed.
Lemma lem4354010 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t t' x''') (h2 : term215 A B s' s t' t) : False.
Proof. exact (EQ_MP (@lem4354009) (@lem4354006 A B x''' s' s t' t h1 h2)). Qed.
Lemma lem4354012 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (proj1 (@lem4344417 A s' s x'' h1)). Qed.
Lemma lem4354013 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term762 A s' x''.
Proof. exact (fun h0 : term99 A s' x'' => @lem4354012 A s' s x'' h1). Qed.
Lemma lem4354015 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4354016 {A : Type'} (s' : A -> Prop) (x'' : A) : (term762 A s' x'') = (s' x'').
Proof. exact (@lem4354015 (s' x'')). Qed.
Lemma lem4354017 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : s' x''.
Proof. exact (EQ_MP (@lem4354016 A s' x'') (@lem4354013 A s' s x'' h1)). Qed.
Lemma lem4354023 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4354024 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : (term163 A s' s _49785) = (term765 A s s' _49785).
Proof. exact (@lem4354023 (s _49785) (term99 A s' _49785)). Qed.
Lemma lem4354030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354031 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : (term766 A s' s _49785) = (term767 A s s' _49785).
Proof. exact (MK_COMB (@lem4354030) (@lem4354024 A s s' _49785)). Qed.
Lemma lem4354037 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : (term765 A s s' _49785) = (term765 A s s' _49785).
Proof. exact (eq_refl (term765 A s s' _49785)). Qed.
Lemma lem4354038 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : ((term163 A s' s _49785) = (term765 A s s' _49785)) = ((term765 A s s' _49785) = (term765 A s s' _49785)).
Proof. exact (MK_COMB (@lem4354031 A s s' _49785) (@lem4354037 A s s' _49785)). Qed.
Lemma lem4354040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4354041 (x : Prop) : (x = x) = True.
Proof. exact (@lem4354040 Prop x). Qed.
Lemma lem4354042 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : ((term765 A s s' _49785) = (term765 A s s' _49785)) = True.
Proof. exact (@lem4354041 (term765 A s s' _49785)). Qed.
Lemma lem4354043 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : ((term163 A s' s _49785) = (term765 A s s' _49785)) = True.
Proof. exact (TRANS (@lem4354038 A s s' _49785) (@lem4354042 A s s' _49785)). Qed.
Lemma lem4354044 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : True = ((term163 A s' s _49785) = (term765 A s s' _49785)).
Proof. exact (SYM (@lem4354043 A s s' _49785)). Qed.
Lemma lem4354045 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (_49785 : A) : (term163 A s' s _49785) = (term765 A s s' _49785).
Proof. exact (EQ_MP (@lem4354044 A s s' _49785) (@lem0)). Qed.
Lemma lem4354046 {A B : Type'} (_49785 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term765 A s s' _49785.
Proof. exact (EQ_MP (@lem4354045 A s s' _49785) (@lem4350590 A B _49785 s' s t' t h1)). Qed.
Lemma lem4354048 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4354049 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49785 : A) : (term765 A s s' _49785) = (term769 A s' s _49785).
Proof. exact (@lem4354048 (term99 A s' _49785) (s _49785)). Qed.
Lemma lem4354051 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4354052 {A : Type'} (s' : A -> Prop) (_49785 : A) : (term151 A s' _49785) = (s' _49785).
Proof. exact (@lem4354051 (s' _49785)). Qed.
Lemma lem4354053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4354054 {A : Type'} (s' : A -> Prop) (_49785 : A) : (term770 A s' _49785) = (term96 A s' _49785).
Proof. exact (MK_COMB (@lem4354053) (@lem4354052 A s' _49785)). Qed.
Lemma lem4354055 {A : Type'} (s : A -> Prop) (_49785 : A) : (s _49785) = (s _49785).
Proof. exact (eq_refl (s _49785)). Qed.
Lemma lem4354056 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49785 : A) : (term769 A s' s _49785) = (term114 A s' s _49785).
Proof. exact (MK_COMB (@lem4354054 A s' _49785) (@lem4354055 A s _49785)). Qed.
Lemma lem4354057 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (_49785 : A) : (term765 A s s' _49785) = (term114 A s' s _49785).
Proof. exact (TRANS (@lem4354049 A s' s _49785) (@lem4354056 A s' s _49785)). Qed.
Lemma lem4354060 {A B : Type'} (_49785 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 A s' s _49785.
Proof. exact (EQ_MP (@lem4354057 A s' s _49785) (@lem4354046 A B _49785 s' s t' t h1)). Qed.
Lemma lem4354061 {A B : Type'} (_49785 : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 A s' s _49785.
Proof. exact (@lem4354060 A B _49785 s' s t' t h1). Qed.
Lemma lem4354062 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 A s' s x''.
Proof. exact (@lem4354061 A B x'' s' s t' t h1). Qed.
Lemma lem4354065 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s' s x'') (h2 : term215 A B s' s t' t) : s x''.
Proof. exact (@lem4354062 A B x'' s' s t' t h2 (@lem4354017 A s' s x'' h1)). Qed.
Lemma lem4354066 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s' s x'') (h2 : term215 A B s' s t' t) : term762 A s x''.
Proof. exact (fun h0 : term99 A s x'' => @lem4354065 A B x'' s' s t' t h1 h2). Qed.
Lemma lem4354068 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4354069 {A : Type'} (s : A -> Prop) (x'' : A) : (term762 A s x'') = (s x'').
Proof. exact (@lem4354068 (s x'')). Qed.
Lemma lem4354070 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s' s x'') (h2 : term215 A B s' s t' t) : s x''.
Proof. exact (EQ_MP (@lem4354069 A s x'') (@lem4354066 A B x'' s' s t' t h1 h2)). Qed.
Lemma lem4354073 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4354075 {A : Type'} (s : A -> Prop) (x'' : A) : (term99 A s x'') = (term98 A s x'').
Proof. exact (@lem4354073 (s x'')). Qed.
Lemma lem4354078 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term162 A s' s x'') : term98 A s x''.
Proof. exact (EQ_MP (@lem4354075 A s x'') (@lem4350598 A s' s x'' h1)). Qed.
Lemma lem4354081 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s' s x'') (h2 : term215 A B s' s t' t) : False.
Proof. exact (@lem4354078 A s' s x'' h1 (@lem4354070 A B x'' s' s t' t h1 h2)). Qed.
Lemma lem4354082 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s' s x'') (h2 : term215 A B s' s t' t) : term764.
Proof. exact (fun h0 : ~ False => @lem4354081 A B x'' s' s t' t h1 h2). Qed.
Lemma lem4354084 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4354085 : term764 = False.
Proof. exact (@lem4354084 False). Qed.
Lemma lem4354086 {A B : Type'} (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 A s' s x'') (h2 : term215 A B s' s t' t) : False.
Proof. exact (EQ_MP (@lem4354085) (@lem4354082 A B x'' s' s t' t h1 h2)). Qed.
Lemma lem4354088 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (proj1 (@lem4344418 B t' t x''' h1)). Qed.
Lemma lem4354089 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term762 B t' x'''.
Proof. exact (fun h0 : term99 B t' x''' => @lem4354088 B t' t x''' h1). Qed.
Lemma lem4354091 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4354092 {B : Type'} (t' : B -> Prop) (x''' : B) : (term762 B t' x''') = (t' x''').
Proof. exact (@lem4354091 (t' x''')). Qed.
Lemma lem4354093 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : t' x'''.
Proof. exact (EQ_MP (@lem4354092 B t' x''') (@lem4354089 B t' t x''' h1)). Qed.
Lemma lem4354099 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4354100 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : (term163 B t' t _49787) = (term765 B t t' _49787).
Proof. exact (@lem4354099 (t _49787) (term99 B t' _49787)). Qed.
Lemma lem4354106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4354107 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : (term766 B t' t _49787) = (term767 B t t' _49787).
Proof. exact (MK_COMB (@lem4354106) (@lem4354100 B t t' _49787)). Qed.
Lemma lem4354113 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : (term765 B t t' _49787) = (term765 B t t' _49787).
Proof. exact (eq_refl (term765 B t t' _49787)). Qed.
Lemma lem4354114 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : ((term163 B t' t _49787) = (term765 B t t' _49787)) = ((term765 B t t' _49787) = (term765 B t t' _49787)).
Proof. exact (MK_COMB (@lem4354107 B t t' _49787) (@lem4354113 B t t' _49787)). Qed.
Lemma lem4354116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4354117 (x : Prop) : (x = x) = True.
Proof. exact (@lem4354116 Prop x). Qed.
Lemma lem4354118 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : ((term765 B t t' _49787) = (term765 B t t' _49787)) = True.
Proof. exact (@lem4354117 (term765 B t t' _49787)). Qed.
Lemma lem4354119 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : ((term163 B t' t _49787) = (term765 B t t' _49787)) = True.
Proof. exact (TRANS (@lem4354114 B t t' _49787) (@lem4354118 B t t' _49787)). Qed.
Lemma lem4354120 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : True = ((term163 B t' t _49787) = (term765 B t t' _49787)).
Proof. exact (SYM (@lem4354119 B t t' _49787)). Qed.
Lemma lem4354121 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (_49787 : B) : (term163 B t' t _49787) = (term765 B t t' _49787).
Proof. exact (EQ_MP (@lem4354120 B t t' _49787) (@lem0)). Qed.
Lemma lem4354122 {A B : Type'} (_49787 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term765 B t t' _49787.
Proof. exact (EQ_MP (@lem4354121 B t t' _49787) (@lem4350610 A B _49787 s' s t' t h1)). Qed.
Lemma lem4354124 (b : Prop) (a : Prop) : (a \/ b) = (term768 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4354125 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49787 : B) : (term765 B t t' _49787) = (term769 B t' t _49787).
Proof. exact (@lem4354124 (term99 B t' _49787) (t _49787)). Qed.
Lemma lem4354127 (a : Prop) : (term148 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4354128 {B : Type'} (t' : B -> Prop) (_49787 : B) : (term151 B t' _49787) = (t' _49787).
Proof. exact (@lem4354127 (t' _49787)). Qed.
Lemma lem4354129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4354130 {B : Type'} (t' : B -> Prop) (_49787 : B) : (term770 B t' _49787) = (term96 B t' _49787).
Proof. exact (MK_COMB (@lem4354129) (@lem4354128 B t' _49787)). Qed.
Lemma lem4354131 {B : Type'} (t : B -> Prop) (_49787 : B) : (t _49787) = (t _49787).
Proof. exact (eq_refl (t _49787)). Qed.
Lemma lem4354132 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49787 : B) : (term769 B t' t _49787) = (term114 B t' t _49787).
Proof. exact (MK_COMB (@lem4354130 B t' _49787) (@lem4354131 B t _49787)). Qed.
Lemma lem4354133 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (_49787 : B) : (term765 B t t' _49787) = (term114 B t' t _49787).
Proof. exact (TRANS (@lem4354125 B t' t _49787) (@lem4354132 B t' t _49787)). Qed.
Lemma lem4354136 {A B : Type'} (_49787 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 B t' t _49787.
Proof. exact (EQ_MP (@lem4354133 B t' t _49787) (@lem4354122 A B _49787 s' s t' t h1)). Qed.
Lemma lem4354137 {A B : Type'} (_49787 : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 B t' t _49787.
Proof. exact (@lem4354136 A B _49787 s' s t' t h1). Qed.
Lemma lem4354138 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) : term114 B t' t x'''.
Proof. exact (@lem4354137 A B x''' s' s t' t h1). Qed.
Lemma lem4354141 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t' t x''') (h2 : term215 A B s' s t' t) : t x'''.
Proof. exact (@lem4354138 A B x''' s' s t' t h2 (@lem4354093 B t' t x''' h1)). Qed.
Lemma lem4354142 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t' t x''') (h2 : term215 A B s' s t' t) : term762 B t x'''.
Proof. exact (fun h0 : term99 B t x''' => @lem4354141 A B x''' s' s t' t h1 h2). Qed.
Lemma lem4354144 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4354145 {B : Type'} (t : B -> Prop) (x''' : B) : (term762 B t x''') = (t x''').
Proof. exact (@lem4354144 (t x''')). Qed.
Lemma lem4354146 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t' t x''') (h2 : term215 A B s' s t' t) : t x'''.
Proof. exact (EQ_MP (@lem4354145 B t x''') (@lem4354142 A B x''' s' s t' t h1 h2)). Qed.
Lemma lem4354149 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4354151 {B : Type'} (t : B -> Prop) (x''' : B) : (term99 B t x''') = (term98 B t x''').
Proof. exact (@lem4354149 (t x''')). Qed.
Lemma lem4354154 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term162 B t' t x''') : term98 B t x'''.
Proof. exact (EQ_MP (@lem4354151 B t x''') (@lem4350630 B t' t x''' h1)). Qed.
Lemma lem4354157 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t' t x''') (h2 : term215 A B s' s t' t) : False.
Proof. exact (@lem4354154 B t' t x''' h1 (@lem4354146 A B x''' s' s t' t h1 h2)). Qed.
Lemma lem4354158 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t' t x''') (h2 : term215 A B s' s t' t) : term764.
Proof. exact (fun h0 : ~ False => @lem4354157 A B x''' s' s t' t h1 h2). Qed.
Lemma lem4354160 (p : Prop) : (term763 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4354161 : term764 = False.
Proof. exact (@lem4354160 False). Qed.
Lemma lem4354162 {A B : Type'} (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term162 B t' t x''') (h2 : term215 A B s' s t' t) : False.
Proof. exact (EQ_MP (@lem4354161) (@lem4354158 A B x''' s' s t' t h1 h2)). Qed.
Lemma lem4354163 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4353858 B t' t x''' h1 h2) (fun h3 : False => @lem4347951 B t' h1)). Qed.
Lemma lem4354164 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4354163 B t' t x''' h1 h2) (@lem4347951 B t' h1)). Qed.
Lemma lem4354165 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4353833 A B x x' s' s x'' t' t x''' h1 h2) (fun h3 : False => @lem4347921 B t' h1)). Qed.
Lemma lem4354166 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4354165 A B x x' s' s x'' t' t x''' h1 h2) (@lem4347921 B t' h1)). Qed.
Lemma lem4354167 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4353808 B t t' x''' h1 h2) (fun h3 : False => @lem4347898 B t h1)). Qed.
Lemma lem4354168 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4354167 B t t' x''' h1 h2) (@lem4347898 B t h1)). Qed.
Lemma lem4354169 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4353783 A B x x' s s' x'' t t' x''' h1 h2) (fun h3 : False => @lem4347868 B t h1)). Qed.
Lemma lem4354170 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4354169 A B x x' s s' x'' t t' x''' h1 h2) (@lem4347868 B t h1)). Qed.
Lemma lem4354171 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4353758 B t' t x''' h1 h2) (fun h3 : False => @lem4347831 B t' h1)). Qed.
Lemma lem4354172 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4354171 B t' t x''' h1 h2) (@lem4347831 B t' h1)). Qed.
Lemma lem4354173 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4353733 A B x x' s' s x'' t' t x''' h1 h2) (fun h3 : False => @lem4347801 B t' h1)). Qed.
Lemma lem4354174 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4354173 A B x x' s' s x'' t' t x''' h1 h2) (@lem4347801 B t' h1)). Qed.
Lemma lem4354175 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4353708 A B x x' s s' x'' t t' x''' h1 h2) (fun h3 : False => @lem4347778 A s h1)). Qed.
Lemma lem4354176 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4354175 A B x x' s s' x'' t t' x''' h1 h2) (@lem4347778 A s h1)). Qed.
Lemma lem4354177 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4353683 A s s' x'' h1 h2) (fun h3 : False => @lem4347748 A s h1)). Qed.
Lemma lem4354178 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4354177 A s s' x'' h1 h2) (@lem4347748 A s h1)). Qed.
Lemma lem4354179 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4353658 A B x x' s' s x'' t' t x''' h1 h2) (fun h3 : False => @lem4347711 A s' h1)). Qed.
Lemma lem4354180 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4354179 A B x x' s' s x'' t' t x''' h1 h2) (@lem4347711 A s' h1)). Qed.
Lemma lem4354181 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4353633 A s' s x'' h1 h2) (fun h3 : False => @lem4347681 A s' h1)). Qed.
Lemma lem4354182 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4354181 A s' s x'' h1 h2) (@lem4347681 A s' h1)). Qed.
Lemma lem4354183 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4353608 B t t' x''' h1 h2) (fun h3 : False => @lem4347658 B t h1)). Qed.
Lemma lem4354184 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4354183 B t t' x''' h1 h2) (@lem4347658 B t h1)). Qed.
Lemma lem4354185 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4353583 A B x x' s s' x'' t t' x''' h1 h2) (fun h3 : False => @lem4347628 B t h1)). Qed.
Lemma lem4354186 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4354185 A B x x' s s' x'' t t' x''' h1 h2) (@lem4347628 B t h1)). Qed.
Lemma lem4354187 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4353558 A B x x' s' s x'' t' t x''' h1 h2) (fun h3 : False => @lem4347591 A s' h1)). Qed.
Lemma lem4354188 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (EQ_MP (@lem4354187 A B x x' s' s x'' t' t x''' h1 h2) (@lem4347591 A s' h1)). Qed.
Lemma lem4354189 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4353533 A s' s x'' h1 h2) (fun h3 : False => @lem4347561 A s' h1)). Qed.
Lemma lem4354190 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4354189 A s' s x'' h1 h2) (@lem4347561 A s' h1)). Qed.
Lemma lem4354191 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4353508 A B x x' s s' x'' t t' x''' h1 h2) (fun h3 : False => @lem4347538 A s h1)). Qed.
Lemma lem4354192 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (EQ_MP (@lem4354191 A B x x' s s' x'' t t' x''' h1 h2) (@lem4347538 A s h1)). Qed.
Lemma lem4354193 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4353483 A s s' x'' h1 h2) (fun h3 : False => @lem4347508 A s h1)). Qed.
Lemma lem4354194 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4354193 A s s' x'' h1 h2) (@lem4347508 A s h1)). Qed.
Lemma lem4354195 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4352774 A B s x t x' h1 h2) (fun h3 : False => @lem4346885 B t h1)). Qed.
Lemma lem4354196 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354195 A B s x t x' h1 h2) (@lem4346885 B t h1)). Qed.
Lemma lem4354197 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4352749 B t t' x''' h1 h2) (fun h3 : False => @lem4346836 B t h1)). Qed.
Lemma lem4354198 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4354197 B t t' x''' h1 h2) (@lem4346836 B t h1)). Qed.
Lemma lem4354199 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4352724 A B s x t x' h1 h2) (fun h3 : False => @lem4346787 B t h1)). Qed.
Lemma lem4354200 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354199 A B s x t x' h1 h2) (@lem4346787 B t h1)). Qed.
Lemma lem4354201 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4352623 A B s x t x' h1 h2) (fun h3 : False => @lem4346689 B t h1)). Qed.
Lemma lem4354202 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354201 A B s x t x' h1 h2) (@lem4346689 B t h1)). Qed.
Lemma lem4354203 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h4 : term102 B t => @lem4352598 A B s t s' x t' x' h1 h2 h3) (fun h4 : False => @lem4346640 B t h1)). Qed.
Lemma lem4354204 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354203 A B s t s' x t' x' h1 h2 h3) (@lem4346640 B t h1)). Qed.
Lemma lem4354205 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4352520 A B s x t x' h1 h2) (fun h3 : False => @lem4346591 B t h1)). Qed.
Lemma lem4354206 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354205 A B s x t x' h1 h2) (@lem4346591 B t h1)). Qed.
Lemma lem4354207 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4352419 A B s x t x' h1 h2) (fun h3 : False => @lem4346493 A s h1)). Qed.
Lemma lem4354208 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354207 A B s x t x' h1 h2) (@lem4346493 A s h1)). Qed.
Lemma lem4354209 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h4 : term102 A s => @lem4352394 A B s t s' x t' x' h1 h2 h3) (fun h4 : False => @lem4346444 A s h1)). Qed.
Lemma lem4354210 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354209 A B s t s' x t' x' h1 h2 h3) (@lem4346444 A s h1)). Qed.
Lemma lem4354211 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4352316 A B s x t x' h1 h2) (fun h3 : False => @lem4346395 A s h1)). Qed.
Lemma lem4354212 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354211 A B s x t x' h1 h2) (@lem4346395 A s h1)). Qed.
Lemma lem4354213 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4352215 A B s x t x' h1 h2) (fun h3 : False => @lem4346297 A s h1)). Qed.
Lemma lem4354214 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354213 A B s x t x' h1 h2) (@lem4346297 A s h1)). Qed.
Lemma lem4354215 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4352190 A s s' x'' h1 h2) (fun h3 : False => @lem4346248 A s h1)). Qed.
Lemma lem4354216 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4354215 A s s' x'' h1 h2) (@lem4346248 A s h1)). Qed.
Lemma lem4354217 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4352165 A B s x t x' h1 h2) (fun h3 : False => @lem4346199 A s h1)). Qed.
Lemma lem4354218 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354217 A B s x t x' h1 h2) (@lem4346199 A s h1)). Qed.
Lemma lem4354219 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4352140 A B s' x t' x' h1 h2) (fun h3 : False => @lem4346124 B t' h1)). Qed.
Lemma lem4354220 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354219 A B s' x t' x' h1 h2) (@lem4346124 B t' h1)). Qed.
Lemma lem4354221 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4352115 B t' t x''' h1 h2) (fun h3 : False => @lem4346075 B t' h1)). Qed.
Lemma lem4354222 {B : Type'} (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') : False.
Proof. exact (EQ_MP (@lem4354221 B t' t x''' h1 h2) (@lem4346075 B t' h1)). Qed.
Lemma lem4354223 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4352090 A B s' x t' x' h1 h2) (fun h3 : False => @lem4346026 B t' h1)). Qed.
Lemma lem4354224 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354223 A B s' x t' x' h1 h2) (@lem4346026 B t' h1)). Qed.
Lemma lem4354225 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351989 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345928 B t' h1)). Qed.
Lemma lem4354226 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354225 A B s' x t' x' h1 h2) (@lem4345928 B t' h1)). Qed.
Lemma lem4354227 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h4 : term102 B t' => @lem4351964 A B s' t' s x t x' h1 h2 h3) (fun h4 : False => @lem4345879 B t' h1)). Qed.
Lemma lem4354228 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354227 A B s' t' s x t x' h1 h2 h3) (@lem4345879 B t' h1)). Qed.
Lemma lem4354229 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351886 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345830 B t' h1)). Qed.
Lemma lem4354230 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354229 A B s' x t' x' h1 h2) (@lem4345830 B t' h1)). Qed.
Lemma lem4354231 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351785 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345751 B t' h1)). Qed.
Lemma lem4354232 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354231 A B s' x t' x' h1 h2) (@lem4345751 B t' h1)). Qed.
Lemma lem4354233 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4351760 A B s x t x' h1 h2) (fun h3 : False => @lem4345728 B t h1)). Qed.
Lemma lem4354234 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354233 A B s x t x' h1 h2) (@lem4345728 B t h1)). Qed.
Lemma lem4354235 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4351735 B t t' x''' h1 h2) (fun h3 : False => @lem4345698 B t h1)). Qed.
Lemma lem4354236 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4354235 B t t' x''' h1 h2) (@lem4345698 B t h1)). Qed.
Lemma lem4354237 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4351710 A B s x t x' h1 h2) (fun h3 : False => @lem4345668 B t h1)). Qed.
Lemma lem4354238 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354237 A B s x t x' h1 h2) (@lem4345668 B t h1)). Qed.
Lemma lem4354239 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351685 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345631 B t' h1)). Qed.
Lemma lem4354240 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354239 A B s' x t' x' h1 h2) (@lem4345631 B t' h1)). Qed.
Lemma lem4354241 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4351660 A B s x t x' h1 h2) (fun h3 : False => @lem4345608 B t h1)). Qed.
Lemma lem4354242 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354241 A B s x t x' h1 h2) (@lem4345608 B t h1)). Qed.
Lemma lem4354243 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351635 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345571 B t' h1)). Qed.
Lemma lem4354244 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354243 A B s' x t' x' h1 h2) (@lem4345571 B t' h1)). Qed.
Lemma lem4354245 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4351610 A B s x t x' h1 h2) (fun h3 : False => @lem4345548 B t h1)). Qed.
Lemma lem4354246 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354245 A B s x t x' h1 h2) (@lem4345548 B t h1)). Qed.
Lemma lem4354247 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351585 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345511 B t' h1)). Qed.
Lemma lem4354248 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354247 A B s' x t' x' h1 h2) (@lem4345511 B t' h1)). Qed.
Lemma lem4354249 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4351560 A B s x t x' h1 h2) (fun h3 : False => @lem4345488 A s h1)). Qed.
Lemma lem4354250 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354249 A B s x t x' h1 h2) (@lem4345488 A s h1)). Qed.
Lemma lem4354251 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351535 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345451 B t' h1)). Qed.
Lemma lem4354252 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354251 A B s' x t' x' h1 h2) (@lem4345451 B t' h1)). Qed.
Lemma lem4354253 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4351510 A B s x t x' h1 h2) (fun h3 : False => @lem4345428 A s h1)). Qed.
Lemma lem4354254 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354253 A B s x t x' h1 h2) (@lem4345428 A s h1)). Qed.
Lemma lem4354255 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : (term102 B t') = False.
Proof. exact (prop_ext (fun h3 : term102 B t' => @lem4351485 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345391 B t' h1)). Qed.
Lemma lem4354256 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 B t') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354255 A B s' x t' x' h1 h2) (@lem4345391 B t' h1)). Qed.
Lemma lem4354257 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4351460 A B s x t x' h1 h2) (fun h3 : False => @lem4345368 A s h1)). Qed.
Lemma lem4354258 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354257 A B s x t x' h1 h2) (@lem4345368 A s h1)). Qed.
Lemma lem4354259 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4351435 A s s' x'' h1 h2) (fun h3 : False => @lem4345338 A s h1)). Qed.
Lemma lem4354260 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4354259 A s s' x'' h1 h2) (@lem4345338 A s h1)). Qed.
Lemma lem4354261 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4351410 A B s x t x' h1 h2) (fun h3 : False => @lem4345308 A s h1)). Qed.
Lemma lem4354262 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354261 A B s x t x' h1 h2) (@lem4345308 A s h1)). Qed.
Lemma lem4354263 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4351385 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345252 A s' h1)). Qed.
Lemma lem4354264 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354263 A B s' x t' x' h1 h2) (@lem4345252 A s' h1)). Qed.
Lemma lem4354265 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h4 : term102 A s' => @lem4351360 A B s' t' s x t x' h1 h2 h3) (fun h4 : False => @lem4345203 A s' h1)). Qed.
Lemma lem4354266 {A B : Type'} (s' : A -> Prop) (t' : B -> Prop) (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354265 A B s' t' s x t x' h1 h2 h3) (@lem4345203 A s' h1)). Qed.
Lemma lem4354267 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4351282 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345154 A s' h1)). Qed.
Lemma lem4354268 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354267 A B s' x t' x' h1 h2) (@lem4345154 A s' h1)). Qed.
Lemma lem4354269 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4351181 A B s' x t' x' h1 h2) (fun h3 : False => @lem4345056 A s' h1)). Qed.
Lemma lem4354270 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354269 A B s' x t' x' h1 h2) (@lem4345056 A s' h1)). Qed.
Lemma lem4354271 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4351156 A s' s x'' h1 h2) (fun h3 : False => @lem4345007 A s' h1)). Qed.
Lemma lem4354272 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term162 A s' s x'') : False.
Proof. exact (EQ_MP (@lem4354271 A s' s x'' h1 h2) (@lem4345007 A s' h1)). Qed.
Lemma lem4354273 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4351131 A B s' x t' x' h1 h2) (fun h3 : False => @lem4344958 A s' h1)). Qed.
Lemma lem4354274 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354273 A B s' x t' x' h1 h2) (@lem4344958 A s' h1)). Qed.
Lemma lem4354275 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4351030 A B s' x t' x' h1 h2) (fun h3 : False => @lem4344879 A s' h1)). Qed.
Lemma lem4354276 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354275 A B s' x t' x' h1 h2) (@lem4344879 A s' h1)). Qed.
Lemma lem4354277 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4351005 A B s x t x' h1 h2) (fun h3 : False => @lem4344856 B t h1)). Qed.
Lemma lem4354278 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354277 A B s x t x' h1 h2) (@lem4344856 B t h1)). Qed.
Lemma lem4354279 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4350980 B t t' x''' h1 h2) (fun h3 : False => @lem4344826 B t h1)). Qed.
Lemma lem4354280 {B : Type'} (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') : False.
Proof. exact (EQ_MP (@lem4354279 B t t' x''' h1 h2) (@lem4344826 B t h1)). Qed.
Lemma lem4354281 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4350955 A B s x t x' h1 h2) (fun h3 : False => @lem4344796 B t h1)). Qed.
Lemma lem4354282 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354281 A B s x t x' h1 h2) (@lem4344796 B t h1)). Qed.
Lemma lem4354283 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4350930 A B s' x t' x' h1 h2) (fun h3 : False => @lem4344759 A s' h1)). Qed.
Lemma lem4354284 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354283 A B s' x t' x' h1 h2) (@lem4344759 A s' h1)). Qed.
Lemma lem4354285 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4350905 A B s x t x' h1 h2) (fun h3 : False => @lem4344736 B t h1)). Qed.
Lemma lem4354286 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354285 A B s x t x' h1 h2) (@lem4344736 B t h1)). Qed.
Lemma lem4354287 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4350880 A B s' x t' x' h1 h2) (fun h3 : False => @lem4344699 A s' h1)). Qed.
Lemma lem4354288 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354287 A B s' x t' x' h1 h2) (@lem4344699 A s' h1)). Qed.
Lemma lem4354289 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : (term102 B t) = False.
Proof. exact (prop_ext (fun h3 : term102 B t => @lem4350855 A B s x t x' h1 h2) (fun h3 : False => @lem4344676 B t h1)). Qed.
Lemma lem4354290 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 B t) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354289 A B s x t x' h1 h2) (@lem4344676 B t h1)). Qed.
Lemma lem4354291 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4350830 A B s' x t' x' h1 h2) (fun h3 : False => @lem4344639 A s' h1)). Qed.
Lemma lem4354292 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354291 A B s' x t' x' h1 h2) (@lem4344639 A s' h1)). Qed.
Lemma lem4354293 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4350805 A B s x t x' h1 h2) (fun h3 : False => @lem4344616 A s h1)). Qed.
Lemma lem4354294 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354293 A B s x t x' h1 h2) (@lem4344616 A s h1)). Qed.
Lemma lem4354295 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4350780 A B s' x t' x' h1 h2) (fun h3 : False => @lem4344579 A s' h1)). Qed.
Lemma lem4354296 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354295 A B s' x t' x' h1 h2) (@lem4344579 A s' h1)). Qed.
Lemma lem4354297 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4350755 A B s x t x' h1 h2) (fun h3 : False => @lem4344556 A s h1)). Qed.
Lemma lem4354298 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354297 A B s x t x' h1 h2) (@lem4344556 A s h1)). Qed.
Lemma lem4354299 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : (term102 A s') = False.
Proof. exact (prop_ext (fun h3 : term102 A s' => @lem4350730 A B s' x t' x' h1 h2) (fun h3 : False => @lem4344519 A s' h1)). Qed.
Lemma lem4354300 {A B : Type'} (s' : A -> Prop) (x : A) (t' : B -> Prop) (x' : B) (h1 : term102 A s') (h2 : term267 A B s' x t' x') : False.
Proof. exact (EQ_MP (@lem4354299 A B s' x t' x' h1 h2) (@lem4344519 A s' h1)). Qed.
Lemma lem4354301 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4350705 A B s x t x' h1 h2) (fun h3 : False => @lem4344496 A s h1)). Qed.
Lemma lem4354302 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354301 A B s x t x' h1 h2) (@lem4344496 A s h1)). Qed.
Lemma lem4354303 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4350680 A s s' x'' h1 h2) (fun h3 : False => @lem4344466 A s h1)). Qed.
Lemma lem4354304 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term162 A s s' x'') : False.
Proof. exact (EQ_MP (@lem4354303 A s s' x'' h1 h2) (@lem4344466 A s h1)). Qed.
Lemma lem4354305 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : (term102 A s) = False.
Proof. exact (prop_ext (fun h3 : term102 A s => @lem4350655 A B s x t x' h1 h2) (fun h3 : False => @lem4344436 A s h1)). Qed.
Lemma lem4354306 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (x' : B) (h1 : term102 A s) (h2 : term267 A B s x t x') : False.
Proof. exact (EQ_MP (@lem4354305 A B s x t x' h1 h2) (@lem4344436 A s h1)). Qed.
Lemma lem4354307 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term535 A B x x' s' s x'' t' t x''') (h2 : term215 A B s' s t' t) : False.
Proof. exact (or_elim (@lem4344415 A B x x' s' s x'' t' t x''' h1) (fun h0 : term162 A s' s x'' => @lem4354086 A B x'' s' s t' t h0 h2) (fun h0 : term162 B t' t x''' => @lem4354162 A B x''' s' s t' t h0 h2)). Qed.
Lemma lem4354308 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term535 A B x x' s s' x'' t t' x''') (h2 : term215 A B s' s t' t) : False.
Proof. exact (or_elim (@lem4344405 A B x x' s s' x'' t t' x''' h1) (fun h0 : term162 A s s' x'' => @lem4353934 A B x'' s' s t' t h0 h2) (fun h0 : term162 B t t' x''' => @lem4354010 A B x''' s' s t' t h0 h2)). Qed.
Lemma lem4354309 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term215 A B s' s t' t) (h2 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344296 A B x x' x'' x''' s' s t' t h2) (fun h0 : term535 A B x x' s s' x'' t t' x''' => @lem4354308 A B x x' x'' x''' s' s t' t h0 h1) (fun h0 : term535 A B x x' s' s x'' t' t x''' => @lem4354307 A B x x' x'' x''' s' s t' t h0 h1)). Qed.
Lemma lem4354310 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4344387 A B x x' s' s x'' t' t x''' h2) (fun h0 : term162 A s' s x'' => @lem4354166 A B x x' s' s x'' t' t x''' h1 h2) (fun h0 : term162 B t' t x''' => @lem4354164 B t' t x''' h1 h0)). Qed.
Lemma lem4354311 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (or_elim (@lem4344377 A B x x' s s' x'' t t' x''' h2) (fun h0 : term162 A s s' x'' => @lem4354170 A B x x' s s' x'' t t' x''' h1 h2) (fun h0 : term162 B t t' x''' => @lem4354168 B t t' x''' h1 h0)). Qed.
Lemma lem4354312 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term102 B t) (h2 : term102 B t') (h3 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344296 A B x x' x'' x''' s' s t' t h3) (fun h0 : term535 A B x x' s s' x'' t t' x''' => @lem4354311 A B x x' s s' x'' t t' x''' h1 h0) (fun h0 : term535 A B x x' s' s x'' t' t x''' => @lem4354310 A B x x' s' s x'' t' t x''' h2 h0)). Qed.
Lemma lem4354313 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4344365 A B x x' s' s x'' t' t x''' h2) (fun h0 : term162 A s' s x'' => @lem4354174 A B x x' s' s x'' t' t x''' h1 h2) (fun h0 : term162 B t' t x''' => @lem4354172 B t' t x''' h1 h0)). Qed.
Lemma lem4354314 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (or_elim (@lem4344355 A B x x' s s' x'' t t' x''' h2) (fun h0 : term162 A s s' x'' => @lem4354178 A s s' x'' h1 h0) (fun h0 : term162 B t t' x''' => @lem4354176 A B x x' s s' x'' t t' x''' h1 h2)). Qed.
Lemma lem4354315 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term102 A s) (h2 : term102 B t') (h3 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344296 A B x x' x'' x''' s' s t' t h3) (fun h0 : term535 A B x x' s s' x'' t t' x''' => @lem4354314 A B x x' s s' x'' t t' x''' h1 h0) (fun h0 : term535 A B x x' s' s x'' t' t x''' => @lem4354313 A B x x' s' s x'' t' t x''' h2 h0)). Qed.
Lemma lem4354316 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term102 B t') (h2 : term127 A B s t s' t') (h3 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344300 A B s t s' t' h2) (fun h0 : term102 A s => @lem4354315 A B x x' x'' x''' s' s t' t h0 h1 h3) (fun h0 : term102 B t => @lem4354312 A B x x' x'' x''' s' s t' t h0 h1 h3)). Qed.
Lemma lem4354317 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4344341 A B x x' s' s x'' t' t x''' h2) (fun h0 : term162 A s' s x'' => @lem4354182 A s' s x'' h1 h0) (fun h0 : term162 B t' t x''' => @lem4354180 A B x x' s' s x'' t' t x''' h1 h2)). Qed.
Lemma lem4354318 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (or_elim (@lem4344331 A B x x' s s' x'' t t' x''' h2) (fun h0 : term162 A s s' x'' => @lem4354186 A B x x' s s' x'' t t' x''' h1 h2) (fun h0 : term162 B t t' x''' => @lem4354184 B t t' x''' h1 h0)). Qed.
Lemma lem4354319 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term102 A s') (h2 : term102 B t) (h3 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344296 A B x x' x'' x''' s' s t' t h3) (fun h0 : term535 A B x x' s s' x'' t t' x''' => @lem4354318 A B x x' s s' x'' t t' x''' h2 h0) (fun h0 : term535 A B x x' s' s x'' t' t x''' => @lem4354317 A B x x' s' s x'' t' t x''' h1 h0)). Qed.
Lemma lem4354320 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term535 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4344319 A B x x' s' s x'' t' t x''' h2) (fun h0 : term162 A s' s x'' => @lem4354190 A s' s x'' h1 h0) (fun h0 : term162 B t' t x''' => @lem4354188 A B x x' s' s x'' t' t x''' h1 h2)). Qed.
Lemma lem4354321 {A B : Type'} (x : A) (x' : B) (s : A -> Prop) (s' : A -> Prop) (x'' : A) (t : B -> Prop) (t' : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term535 A B x x' s s' x'' t t' x''') : False.
Proof. exact (or_elim (@lem4344309 A B x x' s s' x'' t t' x''' h2) (fun h0 : term162 A s s' x'' => @lem4354194 A s s' x'' h1 h0) (fun h0 : term162 B t t' x''' => @lem4354192 A B x x' s s' x'' t t' x''' h1 h2)). Qed.
Lemma lem4354322 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term102 A s) (h2 : term102 A s') (h3 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344296 A B x x' x'' x''' s' s t' t h3) (fun h0 : term535 A B x x' s s' x'' t t' x''' => @lem4354321 A B x x' s s' x'' t t' x''' h1 h0) (fun h0 : term535 A B x x' s' s x'' t' t x''' => @lem4354320 A B x x' s' s x'' t' t x''' h2 h0)). Qed.
Lemma lem4354323 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term102 A s') (h2 : term127 A B s t s' t') (h3 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344300 A B s t s' t' h2) (fun h0 : term102 A s => @lem4354322 A B x x' x'' x''' s' s t' t h0 h1 h3) (fun h0 : term102 B t => @lem4354319 A B x x' x'' x''' s' s t' t h1 h0 h3)). Qed.
Lemma lem4354324 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term127 A B s t s' t') (h2 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344299 A B s t s' t' h1) (fun h0 : term102 A s' => @lem4354323 A B x x' x'' x''' s' s t' t h0 h1 h2) (fun h0 : term102 B t' => @lem4354316 A B x x' x'' x''' s' s t' t h0 h1 h2)). Qed.
Lemma lem4354325 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term672 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4344295 A B x x' x'' x''' s' s t' t h1) (fun h0 : term127 A B s t s' t' => @lem4354324 A B x x' x'' x''' s' s t' t h0 h1) (fun h0 : term215 A B s' s t' t => @lem4354309 A B x x' x'' x''' s' s t' t h0 h1)). Qed.
Lemma lem4354326 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 B t' t x''') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4353382 A B s' s t' t x''' h1 h2) (fun h0 : term267 A B s' x t' x' => @lem4353458 A B s' s t' t x''' h1 h2)). Qed.
Lemma lem4354327 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 B t t' x''') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4353230 A B s s' t t' x''' h1 h2) (fun h0 : term267 A B s' x t' x' => @lem4353306 A B s s' t t' x''' h1 h2)). Qed.
Lemma lem4354328 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4344258 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354327 A B x x' s' s x'' t' t x''' h1 h0 h3) (fun h0 : term162 B t' t x''' => @lem4354326 A B x x' s' s x'' t' t x''' h2 h0 h3)). Qed.
Lemma lem4354329 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term162 A s' s x'') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4353078 A B t' t s' s x'' h1 h2) (fun h0 : term267 A B s' x t' x' => @lem4353154 A B t' t s' s x'' h1 h2)). Qed.
Lemma lem4354330 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term162 A s s' x'') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4352926 A B t t' s s' x'' h1 h2) (fun h0 : term267 A B s' x t' x' => @lem4353002 A B t t' s s' x'' h1 h2)). Qed.
Lemma lem4354331 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term179 A B s s' t t') (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4344257 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354330 A B x x' s' s x'' t' t x''' h1 h0 h3) (fun h0 : term162 A s' s x'' => @lem4354329 A B x x' s' s x'' t' t x''' h2 h0 h3)). Qed.
Lemma lem4354332 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s s' t t') (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354331 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354328 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354333 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term162 B t' t x''') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4354196 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4352850 A B s' s t' t x''' h2 h3)). Qed.
Lemma lem4354334 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354200 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354198 B t t' x''' h1 h2)). Qed.
Lemma lem4354335 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4344218 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354334 A B x x' s' s x'' t' t x''' h1 h0 h3) (fun h0 : term162 B t' t x''' => @lem4354333 A B x x' s' s x'' t' t x''' h1 h2 h0 h3)). Qed.
Lemma lem4354336 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term162 A s' s x'') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4354202 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4352699 A B t' t s' s x'' h2 h3)). Qed.
Lemma lem4354337 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354206 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354204 A B s t s' x t' x' h1 h2 h0)). Qed.
Lemma lem4354338 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4344217 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354337 A B x x' s' s x'' t' t x''' h1 h2 h3) (fun h0 : term162 A s' s x'' => @lem4354336 A B x x' s' s x'' t' t x''' h1 h2 h0 h3)). Qed.
Lemma lem4354339 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354338 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354335 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354340 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term179 A B s' s t' t) (h2 : term436 A B x x' s' s x'' t' t x''') (h3 : term185 A B s s' t t') : False.
Proof. exact (or_elim (@lem4344176 A B s s' t t' h3) (fun h0 : term102 B t => @lem4354339 A B x x' s' s x'' t' t x''' h0 h1 h2) (fun h0 : term179 A B s s' t t' => @lem4354332 A B x x' s' s x'' t' t x''' h0 h1 h2)). Qed.
Lemma lem4354341 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term162 B t' t x''') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4354208 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4352495 A B s' s t' t x''' h2 h3)). Qed.
Lemma lem4354342 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354212 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354210 A B s t s' x t' x' h1 h2 h0)). Qed.
Lemma lem4354343 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4344178 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354342 A B x x' s' s x'' t' t x''' h1 h2 h3) (fun h0 : term162 B t' t x''' => @lem4354341 A B x x' s' s x'' t' t x''' h1 h2 h0 h3)). Qed.
Lemma lem4354344 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term162 A s' s x'') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4354214 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4352291 A B t' t s' s x'' h2 h3)). Qed.
Lemma lem4354345 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term162 A s s' x'') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354218 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354216 A s s' x'' h1 h2)). Qed.
Lemma lem4354346 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4344177 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354345 A B x x' s' s x'' t' t x''' h1 h0 h3) (fun h0 : term162 A s' s x'' => @lem4354344 A B x x' s' s x'' t' t x''' h1 h2 h0 h3)). Qed.
Lemma lem4354347 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term179 A B s' s t' t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354346 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354343 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354348 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term179 A B s' s t' t) (h2 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343928 A B x x' s' s x'' t' t x''' h2) (fun h0 : term102 A s => @lem4354347 A B x x' s' s x'' t' t x''' h0 h1 h2) (fun h0 : term185 A B s s' t t' => @lem4354340 A B x x' x'' x''' s s' t t' h1 h2 h0)). Qed.
Lemma lem4354349 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term162 B t' t x''') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354222 B t' t x''' h1 h2) (fun h0 : term267 A B s' x t' x' => @lem4354220 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354350 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term162 B t t' x''') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4352065 A B s s' t t' x''' h2 h3) (fun h0 : term267 A B s' x t' x' => @lem4354224 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354351 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4344136 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354350 A B x x' s' s x'' t' t x''' h1 h2 h0 h3) (fun h0 : term162 B t' t x''' => @lem4354349 A B x x' s' s x'' t' t x''' h1 h0 h3)). Qed.
Lemma lem4354352 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354228 A B s' t' s x t x' h1 h2 h0) (fun h0 : term267 A B s' x t' x' => @lem4354226 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354353 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term162 A s s' x'') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4351861 A B t t' s s' x'' h2 h3) (fun h0 : term267 A B s' x t' x' => @lem4354230 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354354 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4344135 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354353 A B x x' s' s x'' t' t x''' h1 h2 h0 h3) (fun h0 : term162 A s' s x'' => @lem4354352 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354355 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354354 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354351 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354356 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354234 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354232 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354357 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354238 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354236 B t t' x''' h1 h2)). Qed.
Lemma lem4354358 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4344096 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354357 A B x x' s' s x'' t' t x''' h1 h0 h3) (fun h0 : term162 B t' t x''' => @lem4354356 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354359 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354242 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354240 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354360 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354246 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354244 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354361 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 B t) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4344095 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354360 A B x x' s' s x'' t' t x''' h1 h2 h3) (fun h0 : term162 A s' s x'' => @lem4354359 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354362 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354361 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354358 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354363 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term102 B t') (h2 : term436 A B x x' s' s x'' t' t x''') (h3 : term185 A B s s' t t') : False.
Proof. exact (or_elim (@lem4344054 A B s s' t t' h3) (fun h0 : term102 B t => @lem4354362 A B x x' s' s x'' t' t x''' h0 h1 h2) (fun h0 : term179 A B s s' t t' => @lem4354355 A B x x' s' s x'' t' t x''' h1 h0 h2)). Qed.
Lemma lem4354364 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354250 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354248 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354365 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354254 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354252 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354366 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4344056 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354365 A B x x' s' s x'' t' t x''' h1 h2 h3) (fun h0 : term162 B t' t x''' => @lem4354364 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354367 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354258 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354256 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354368 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term162 A s s' x'') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354262 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354260 A s s' x'' h1 h2)). Qed.
Lemma lem4354369 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4344055 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354368 A B x x' s' s x'' t' t x''' h1 h0 h3) (fun h0 : term162 A s' s x'' => @lem4354367 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354370 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 B t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354369 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354366 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354371 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t') (h2 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343928 A B x x' s' s x'' t' t x''' h2) (fun h0 : term102 A s => @lem4354370 A B x x' s' s x'' t' t x''' h0 h1 h2) (fun h0 : term185 A B s s' t t' => @lem4354363 A B x x' x'' x''' s s' t t' h1 h2 h0)). Qed.
Lemma lem4354372 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term436 A B x x' s' s x'' t' t x''') (h2 : term185 A B s' s t' t) : False.
Proof. exact (or_elim (@lem4343930 A B s' s t' t h2) (fun h0 : term102 B t' => @lem4354371 A B x x' s' s x'' t' t x''' h0 h1) (fun h0 : term179 A B s' s t' t => @lem4354348 A B x x' s' s x'' t' t x''' h0 h1)). Qed.
Lemma lem4354373 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354266 A B s' t' s x t x' h1 h2 h0) (fun h0 : term267 A B s' x t' x' => @lem4354264 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354374 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term162 B t t' x''') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4351257 A B s s' t t' x''' h2 h3) (fun h0 : term267 A B s' x t' x' => @lem4354268 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354375 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4344014 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354374 A B x x' s' s x'' t' t x''' h1 h2 h0 h3) (fun h0 : term162 B t' t x''' => @lem4354373 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354376 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term162 A s' s x'') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354272 A s' s x'' h1 h2) (fun h0 : term267 A B s' x t' x' => @lem4354270 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354377 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term162 A s s' x'') (h4 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h4) (fun h0 : term267 A B s x t x' => @lem4351106 A B t t' s s' x'' h2 h3) (fun h0 : term267 A B s' x t' x' => @lem4354274 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354378 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4344013 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354377 A B x x' s' s x'' t' t x''' h1 h2 h0 h3) (fun h0 : term162 A s' s x'' => @lem4354376 A B x x' s' s x'' t' t x''' h1 h0 h3)). Qed.
Lemma lem4354379 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term179 A B s s' t t') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354378 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354375 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354380 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term102 B t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354278 A B s x t x' h2 h0) (fun h0 : term267 A B s' x t' x' => @lem4354276 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354381 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 B t) (h2 : term162 B t t' x''') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354282 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354280 B t t' x''' h1 h2)). Qed.
Lemma lem4354382 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term102 B t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4343974 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354381 A B x x' s' s x'' t' t x''' h2 h0 h3) (fun h0 : term162 B t' t x''' => @lem4354380 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354383 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term102 B t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354286 A B s x t x' h2 h0) (fun h0 : term267 A B s' x t' x' => @lem4354284 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354384 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term102 B t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354290 A B s x t x' h2 h0) (fun h0 : term267 A B s' x t' x' => @lem4354288 A B s' x t' x' h1 h0)). Qed.
Lemma lem4354385 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s') (h2 : term102 B t) (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4343973 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354384 A B x x' s' s x'' t' t x''' h1 h2 h3) (fun h0 : term162 A s' s x'' => @lem4354383 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354386 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term102 B t) (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354385 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354382 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354387 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s : A -> Prop) (s' : A -> Prop) (t : B -> Prop) (t' : B -> Prop) (h1 : term102 A s') (h2 : term436 A B x x' s' s x'' t' t x''') (h3 : term185 A B s s' t t') : False.
Proof. exact (or_elim (@lem4343932 A B s s' t t' h3) (fun h0 : term102 B t => @lem4354386 A B x x' s' s x'' t' t x''' h1 h0 h2) (fun h0 : term179 A B s s' t t' => @lem4354379 A B x x' s' s x'' t' t x''' h1 h0 h2)). Qed.
Lemma lem4354388 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 A s') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354294 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354292 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354389 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 A s') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354298 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354296 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354390 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 A s') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 B t' t x''') : False.
Proof. exact (or_elim (@lem4343934 B t' t x''' h4) (fun h0 : term162 B t t' x''' => @lem4354389 A B x x' s' s x'' t' t x''' h1 h2 h3) (fun h0 : term162 B t' t x''' => @lem4354388 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354391 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 A s') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354302 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354300 A B s' x t' x' h2 h0)). Qed.
Lemma lem4354392 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term162 A s s' x'') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343926 A B x x' s' s x'' t' t x''' h3) (fun h0 : term267 A B s x t x' => @lem4354306 A B s x t x' h1 h0) (fun h0 : term267 A B s' x t' x' => @lem4354304 A s s' x'' h1 h2)). Qed.
Lemma lem4354393 {A B : Type'} (x : A) (x' : B) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (h1 : term102 A s) (h2 : term102 A s') (h3 : term436 A B x x' s' s x'' t' t x''') (h4 : term294 A s' s x'') : False.
Proof. exact (or_elim (@lem4343933 A s' s x'' h4) (fun h0 : term162 A s s' x'' => @lem4354392 A B x x' s' s x'' t' t x''' h1 h0 h3) (fun h0 : term162 A s' s x'' => @lem4354391 A B x x' s' s x'' t' t x''' h1 h2 h3)). Qed.
Lemma lem4354394 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s) (h2 : term102 A s') (h3 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343925 A B x x' s' s x'' t' t x''' h3) (fun h0 : term294 A s' s x'' => @lem4354393 A B x x' t' t x''' s' s x'' h1 h2 h3 h0) (fun h0 : term294 B t' t x''' => @lem4354390 A B x x' s' s x'' t' t x''' h1 h2 h3 h0)). Qed.
Lemma lem4354395 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term102 A s') (h2 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343928 A B x x' s' s x'' t' t x''' h2) (fun h0 : term102 A s => @lem4354394 A B x x' s' s x'' t' t x''' h0 h1 h2) (fun h0 : term185 A B s s' t t' => @lem4354387 A B x x' x'' x''' s s' t t' h1 h2 h0)). Qed.
Lemma lem4354396 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (x'' : A) (t' : B -> Prop) (t : B -> Prop) (x''' : B) (h1 : term436 A B x x' s' s x'' t' t x''') : False.
Proof. exact (or_elim (@lem4343927 A B x x' s' s x'' t' t x''' h1) (fun h0 : term102 A s' => @lem4354395 A B x x' s' s x'' t' t x''' h0 h1) (fun h0 : term185 A B s' s t' t => @lem4354372 A B x x' x'' x''' s' s t' t h1 h0)). Qed.
Lemma lem4354397 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term751 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (or_elim (@lem4343920 A B x x' x'' x''' s' s t' t h1) (fun h0 : term436 A B x x' s' s x'' t' t x''' => @lem4354396 A B x x' s' s x'' t' t x''' h0) (fun h0 : term672 A B x x' x'' x''' s' s t' t => @lem4354325 A B x x' x'' x''' s' s t' t h0)). Qed.
Lemma lem4354398 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term751 A B x x' x'' x''' s' s t' t) : (term751 A B x x' x'' x''' s' s t' t) = False.
Proof. exact (prop_ext (fun h2 : term751 A B x x' x'' x''' s' s t' t => @lem4354397 A B x x' x'' x''' s' s t' t h1) (fun h2 : False => @lem4343920 A B x x' x'' x''' s' s t' t h1)). Qed.
Lemma lem4354399 {A B : Type'} (x : A) (x' : B) (x'' : A) (x''' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term751 A B x x' x'' x''' s' s t' t) : False.
Proof. exact (EQ_MP (@lem4354398 A B x x' x'' x''' s' s t' t h1) (@lem4343920 A B x x' x'' x''' s' s t' t h1)). Qed.
Lemma lem4354400 {A B : Type'} (x : A) (x' : B) (x'' : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term754 A B x x' x'' s' s t' t) : False.
Proof. exact (ex_elim (@lem4343537 A B x x' x'' s' s t' t h1) (fun x''' : B => fun h0 : term753 A B x x' x'' s' s t' t x''' => @lem4354399 A B x x' x'' x''' s' s t' t h0)). Qed.
Lemma lem4354401 {A B : Type'} (x : A) (x' : B) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term756 A B x x' s' s t' t) : False.
Proof. exact (ex_elim (@lem4343536 A B x x' s' s t' t h1) (fun x'' : A => fun h0 : term755 A B x x' s' s t' t x'' => @lem4354400 A B x x' x'' s' s t' t h0)). Qed.
Lemma lem4354402 {A B : Type'} (x : A) (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term758 A B x s' s t' t) : False.
Proof. exact (ex_elim (@lem4343535 A B x s' s t' t h1) (fun x' : B => fun h0 : term757 A B x s' s t' t x' => @lem4354401 A B x x' s' s t' t h0)). Qed.
Lemma lem4354403 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term150 A B s' s t' t) : False.
Proof. exact (ex_elim (@lem4343534 A B s' s t' t h1) (fun x : A => fun h0 : term759 A B s' s t' t x => @lem4354402 A B x s' s t' t h0)). Qed.
Lemma lem4354404 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term150 A B s' s t' t) : (term150 A B s' s t' t) = False.
Proof. exact (prop_ext (fun h2 : term150 A B s' s t' t => @lem4354403 A B s' s t' t h1) (fun h2 : False => @lem4341389 A B s' s t' t h1)). Qed.
Lemma lem4354405 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) (h1 : term150 A B s' s t' t) : False.
Proof. exact (EQ_MP (@lem4354404 A B s' s t' t h1) (@lem4341389 A B s' s t' t h1)). Qed.
Lemma lem4354406 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : term149 A B s' s t' t.
Proof. exact (fun h0 : term150 A B s' s t' t => @lem4354405 A B s' s t' t h0). Qed.
Lemma lem4354407 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t' : B -> Prop) (t : B -> Prop) : (term123 A B s' s t' t) = (term132 A B s' s t' t).
Proof. exact (EQ_MP (@lem4341388 A B s' s t' t) (@lem4354406 A B s' s t' t)). Qed.
Lemma lem4354412 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) (t : B -> Prop) : term134 A B s' s t.
Proof. exact (fun t' : B -> Prop => @lem4354407 A B s' s t' t). Qed.
Lemma lem4354417 {A B : Type'} (s' : A -> Prop) (s : A -> Prop) : term136 A B s' s.
Proof. exact (fun t : B -> Prop => @lem4354412 A B s' s t). Qed.
Lemma lem4354422 {A B : Type'} (s : A -> Prop) : term138 A B s.
Proof. exact (fun s' : A -> Prop => @lem4354417 A B s' s). Qed.
Lemma lem4354427 {A B : Type'} : term140 A B.
Proof. exact (fun s : A -> Prop => @lem4354422 A B s). Qed.
Lemma lem4354428 {A B : Type'} : term142 A B.
Proof. exact (EQ_MP (@lem4341384 A B) (@lem4354427 A B)). Qed.
Lemma lem4354430 {A B : Type'} : term142 A B.
Proof. exact (@lem4340912 A B (@lem4354428 A B)). Qed.
Lemma lem4354431 {A B : Type'} (h1 : term143 A B) : False.
Proof. exact (@lem4354430 A B (@lem4340896 A B h1)). Qed.
Lemma lem4354432 {A B : Type'} (h1 : term143 A B) : (term143 A B) = False.
Proof. exact (prop_ext (fun h2 : term143 A B => @lem4354431 A B h1) (fun h2 : False => @lem4340896 A B h1)). Qed.
Lemma lem4354433 {A B : Type'} (h1 : term143 A B) : False.
Proof. exact (EQ_MP (@lem4354432 A B h1) (@lem4340896 A B h1)). Qed.
Lemma lem4354434 {A B : Type'} : term142 A B.
Proof. exact (fun h0 : term143 A B => @lem4354433 A B h0). Qed.
Lemma lem4354435 {A B : Type'} : term140 A B.
Proof. exact (EQ_MP (@lem4340895 A B) (@lem4354434 A B)). Qed.
Lemma lem4354436 {A B : Type'} : term94 A B.
Proof. exact (EQ_MP (@lem4340891 A B) (@lem4354435 A B)). Qed.
Lemma lem4354437 {A B : Type'} : term63 A B.
Proof. exact (EQ_MP (@lem4339989 A B) (@lem4354436 A B)). Qed.
Lemma lem4354438 {A B : Type'} : term62 A B.
Proof. exact (EQ_MP (@lem4339539 A B) (@lem4354437 A B)). Qed.
