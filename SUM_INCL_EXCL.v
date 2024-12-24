Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_INCL_EXCL_term_abbrevs.
Require Import ITERATE_INCL_EXCL_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7068310 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7068312 {_120960 _120978 : Type'} (h1 : term0 _120960 _120978) : term0 _120960 _120978.
Proof. exact (h1). Qed.
Lemma lem7068313 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) : term1 _120960 _120978 op.
Proof. exact (@lem7068312 _120960 _120978 h1 op). Qed.
Lemma lem7068314 {_120960 _120978 : Type'} (op : type1400 _120978) : (term1 _120960 _120978 op) = (term2 _120960 _120978 op).
Proof. exact (eq_refl (term1 _120960 _120978 op)). Qed.
Lemma lem7068315 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) : term2 _120960 _120978 op.
Proof. exact (EQ_MP (@lem7068314 _120960 _120978 op) (@lem7068313 _120960 _120978 op h1)). Qed.
Lemma lem7068316 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : @monoidal _120978 op.
Proof. exact (h1). Qed.
Lemma lem7068317 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) (h2 : @monoidal _120978 op) : term3 _120960 _120978 op.
Proof. exact (@lem7068315 _120960 _120978 op h1 (@lem7068316 _120978 op h2)). Qed.
Lemma lem7068318 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term4 _120960 _120978 op.
Proof. exact (fun h0 : term0 _120960 _120978 => @lem7068317 _120960 _120978 op h0 h1). Qed.
Lemma lem7068319 {_120960 _120978 : Type'} (h1 : term0 _120960 _120978) : term0 _120960 _120978.
Proof. exact (h1). Qed.
Lemma lem7068320 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) (h2 : @monoidal _120978 op) : term3 _120960 _120978 op.
Proof. exact (@lem7068318 _120960 _120978 op h2 (@lem7068319 _120960 _120978 h1)). Qed.
Lemma lem7068321 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) : term2 _120960 _120978 op.
Proof. exact (fun h0 : @monoidal _120978 op => @lem7068320 _120960 _120978 op h1 h0). Qed.
Lemma lem7068322 {_120960 _120978 : Type'} (h1 : term0 _120960 _120978) : term0 _120960 _120978.
Proof. exact (fun op : type1400 _120978 => @lem7068321 _120960 _120978 op h1). Qed.
Lemma lem7068323 {_120960 _120978 : Type'} : term5 _120960 _120978.
Proof. exact (fun h0 : term0 _120960 _120978 => @lem7068322 _120960 _120978 h0). Qed.
Lemma lem7068324 {_120960 _120978 : Type'} : term0 _120960 _120978.
Proof. exact (@lem7068323 _120960 _120978 (@lem5778669 _120960 _120978)). Qed.
Lemma lem7068325 {_120960 _120978 : Type'} (op : type1400 _120978) : term1 _120960 _120978 op.
Proof. exact (@lem7068324 _120960 _120978 op). Qed.
Lemma lem7068326 {_120960 _120978 : Type'} (op : type1400 _120978) : (term1 _120960 _120978 op) = (term2 _120960 _120978 op).
Proof. exact (eq_refl (term1 _120960 _120978 op)). Qed.
Lemma lem7068353 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068354 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7068353 A). Qed.
Lemma lem7068355 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068356 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7068354 A) (@lem7068355 A s)). Qed.
Lemma lem7068357 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068358 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@iterate real A real_add s f).
Proof. exact (MK_COMB (@lem7068356 A s) (@lem7068357 A f)). Qed.
Lemma lem7068359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7068360 {A : Type'} (s : A -> Prop) (f : A -> real) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7068359) (@lem7068358 A s f)). Qed.
Lemma lem7068362 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068363 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7068362 A). Qed.
Lemma lem7068364 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7068365 {A : Type'} (t : A -> Prop) : (@sum A t) = (@iterate real A real_add t).
Proof. exact (MK_COMB (@lem7068363 A) (@lem7068364 A t)). Qed.
Lemma lem7068366 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068367 {A : Type'} (t : A -> Prop) (f : A -> real) : (@sum A t f) = (@iterate real A real_add t f).
Proof. exact (MK_COMB (@lem7068365 A t) (@lem7068366 A f)). Qed.
Lemma lem7068368 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term8 A s t f) = (term9 A s t f).
Proof. exact (MK_COMB (@lem7068360 A s f) (@lem7068367 A t f)). Qed.
Lemma lem7068369 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7068370 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term10 A s t f) = (term11 A s t f).
Proof. exact (MK_COMB (@lem7068369) (@lem7068368 A s t f)). Qed.
Lemma lem7068372 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068373 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7068372 A). Qed.
Lemma lem7068374 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@UNION A s t).
Proof. exact (eq_refl (@UNION A s t)). Qed.
Lemma lem7068375 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = (term13 A s t).
Proof. exact (MK_COMB (@lem7068373 A) (@lem7068374 A s t)). Qed.
Lemma lem7068376 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068377 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term14 A s t f) = (term15 A s t f).
Proof. exact (MK_COMB (@lem7068375 A s t) (@lem7068376 A f)). Qed.
Lemma lem7068378 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7068379 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term16 A s t f) = (term17 A s t f).
Proof. exact (MK_COMB (@lem7068378) (@lem7068377 A s t f)). Qed.
Lemma lem7068381 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068382 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7068381 A). Qed.
Lemma lem7068383 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@INTER A s t).
Proof. exact (eq_refl (@INTER A s t)). Qed.
Lemma lem7068384 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem7068382 A) (@lem7068383 A s t)). Qed.
Lemma lem7068385 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068386 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term20 A s t f) = (term21 A s t f).
Proof. exact (MK_COMB (@lem7068384 A s t) (@lem7068385 A f)). Qed.
Lemma lem7068387 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term22 A s t f) = (term23 A s t f).
Proof. exact (MK_COMB (@lem7068379 A s t f) (@lem7068386 A s t f)). Qed.
Lemma lem7068388 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : ((term8 A s t f) = (term22 A s t f)) = ((term9 A s t f) = (term23 A s t f)).
Proof. exact (MK_COMB (@lem7068370 A s t f) (@lem7068387 A s t f)). Qed.
Lemma lem7068391 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A s t) = (term24 A s t).
Proof. exact (eq_refl (term24 A s t)). Qed.
Lemma lem7068392 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term25 A s t f) = (term26 A s t f).
Proof. exact (MK_COMB (@lem7068391 A s t) (@lem7068388 A s t f)). Qed.
Lemma lem7068395 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term28 A s t).
Proof. exact (fun_ext (fun f : A -> real => @lem7068392 A s t f)). Qed.
Lemma lem7068396 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7068397 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term30 A s t).
Proof. exact (MK_COMB (@lem7068396 A) (@lem7068395 A s t)). Qed.
Lemma lem7068402 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7068397 A s t)). Qed.
Lemma lem7068403 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7068404 {A : Type'} (s : A -> Prop) : (term33 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem7068403 A) (@lem7068402 A s)). Qed.
Lemma lem7068409 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7068404 A s)). Qed.
Lemma lem7068410 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7068411 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (MK_COMB (@lem7068410 A) (@lem7068409 A)). Qed.
Lemma lem7068416 {A : Type'} : (term38 A) = (term37 A).
Proof. exact (SYM (@lem7068411 A)). Qed.
Lemma lem7068418 {_120960 _120978 : Type'} (op : type1400 _120978) : term2 _120960 _120978 op.
Proof. exact (EQ_MP (@lem7068326 _120960 _120978 op) (@lem7068325 _120960 _120978 op)). Qed.
Lemma lem7068419 {A : Type'} (op : type1627) : term39 A op.
Proof. exact (@lem7068418 A real op). Qed.
Lemma lem7068420 {A : Type'} : term40 A.
Proof. exact (@lem7068419 A real_add). Qed.
Lemma lem7068422 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7068310) (@lem7067132)). Qed.
Lemma lem7068423 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7068422)). Qed.
Lemma lem7068424 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7068423) (@lem0)). Qed.
Lemma lem7068425 {A : Type'} : term38 A.
Proof. exact (@lem7068420 A (@lem7068424)). Qed.
Lemma lem7068426 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem7068416 A) (@lem7068425 A)). Qed.
