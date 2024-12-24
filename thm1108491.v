Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108491_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1108364 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : (ZIP' (@nil _25719)) = (term0 _25719 _25727)) : (ZIP' (@nil _25719)) = (term0 _25719 _25727).
Proof. exact (h1). Qed.
Lemma lem1108365 {_25727 : Type'} (l2 : list _25727) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1108366 {_25719 _25727 : Type'} (l2 : list _25727) (ZIP' : type1134 _25719 _25727) (h1 : (ZIP' (@nil _25719)) = (term0 _25719 _25727)) : (ZIP' (@nil _25719) l2) = (term1 _25719 _25727 l2).
Proof. exact (MK_COMB (@lem1108364 _25719 _25727 ZIP' h1) (@lem1108365 _25727 l2)). Qed.
Lemma lem1108367 {_25719 _25727 : Type'} (l2 : list _25727) : (term1 _25719 _25727 l2) = (@nil (prod _25719 _25727)).
Proof. exact (eq_refl (term1 _25719 _25727 l2)). Qed.
Lemma lem1108368 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (l2 : list _25727) : (term2 _25719 _25727 ZIP' l2) = (term2 _25719 _25727 ZIP' l2).
Proof. exact (eq_refl (term2 _25719 _25727 ZIP' l2)). Qed.
Lemma lem1108369 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (l2 : list _25727) : ((ZIP' (@nil _25719) l2) = (term1 _25719 _25727 l2)) = ((ZIP' (@nil _25719) l2) = (@nil (prod _25719 _25727))).
Proof. exact (MK_COMB (@lem1108368 _25719 _25727 ZIP' l2) (@lem1108367 _25719 _25727 l2)). Qed.
Lemma lem1108370 {_25719 _25727 : Type'} (l2 : list _25727) (ZIP' : type1134 _25719 _25727) (h1 : (ZIP' (@nil _25719)) = (term0 _25719 _25727)) : (ZIP' (@nil _25719) l2) = (@nil (prod _25719 _25727)).
Proof. exact (EQ_MP (@lem1108369 _25719 _25727 ZIP' l2) (@lem1108366 _25719 _25727 l2 ZIP' h1)). Qed.
Lemma lem1108371 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : (ZIP' (@nil _25719)) = (term0 _25719 _25727)) : term3 _25719 _25727 ZIP'.
Proof. exact (fun l2 : list _25727 => @lem1108370 _25719 _25727 l2 ZIP' h1). Qed.
Lemma lem1108372 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : term4 _25719 _25727 ZIP'.
Proof. exact (h1). Qed.
Lemma lem1108373 {_25719 _25727 : Type'} (h1' : _25719) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : term5 _25719 _25727 ZIP' h1'.
Proof. exact (@lem1108372 _25719 _25727 ZIP' h1 h1'). Qed.
Lemma lem1108374 {_25719 _25727 : Type'} (h1' : _25719) (ZIP' : type1134 _25719 _25727) : (term5 _25719 _25727 ZIP' h1') = (term6 _25719 _25727 h1' ZIP').
Proof. exact (eq_refl (term5 _25719 _25727 ZIP' h1')). Qed.
Lemma lem1108375 {_25719 _25727 : Type'} (h1' : _25719) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : term6 _25719 _25727 h1' ZIP'.
Proof. exact (EQ_MP (@lem1108374 _25719 _25727 h1' ZIP') (@lem1108373 _25719 _25727 h1' ZIP' h1)). Qed.
Lemma lem1108376 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : term7 _25719 _25727 h1' ZIP' t1.
Proof. exact (@lem1108375 _25719 _25727 h1' ZIP' h1 t1). Qed.
Lemma lem1108377 {_25719 _25727 : Type'} (h1' : _25719) (ZIP' : type1134 _25719 _25727) (t1 : list _25719) : (term7 _25719 _25727 h1' ZIP' t1) = ((term8 _25719 _25727 ZIP' h1' t1) = (term9 _25719 _25727 h1' ZIP' t1)).
Proof. exact (eq_refl (term7 _25719 _25727 h1' ZIP' t1)). Qed.
Lemma lem1108378 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : (term8 _25719 _25727 ZIP' h1' t1) = (term9 _25719 _25727 h1' ZIP' t1).
Proof. exact (EQ_MP (@lem1108377 _25719 _25727 h1' ZIP' t1) (@lem1108376 _25719 _25727 h1' t1 ZIP' h1)). Qed.
Lemma lem1108379 {_25727 : Type'} (l2 : list _25727) : l2 = l2.
Proof. exact (eq_refl l2). Qed.
Lemma lem1108380 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : (term10 _25719 _25727 ZIP' h1' t1 l2) = (term11 _25719 _25727 h1' ZIP' t1 l2).
Proof. exact (MK_COMB (@lem1108378 _25719 _25727 h1' t1 ZIP' h1) (@lem1108379 _25727 l2)). Qed.
Lemma lem1108381 {_25719 _25727 : Type'} (h1' : _25719) (ZIP' : type1134 _25719 _25727) (t1 : list _25719) (l2 : list _25727) : (term11 _25719 _25727 h1' ZIP' t1 l2) = (term12 _25719 _25727 h1' ZIP' t1 l2).
Proof. exact (eq_refl (term11 _25719 _25727 h1' ZIP' t1 l2)). Qed.
Lemma lem1108382 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : (term13 _25719 _25727 ZIP' h1' t1 l2) = (term13 _25719 _25727 ZIP' h1' t1 l2).
Proof. exact (eq_refl (term13 _25719 _25727 ZIP' h1' t1 l2)). Qed.
Lemma lem1108383 {_25719 _25727 : Type'} (h1' : _25719) (ZIP' : type1134 _25719 _25727) (t1 : list _25719) (l2 : list _25727) : ((term10 _25719 _25727 ZIP' h1' t1 l2) = (term11 _25719 _25727 h1' ZIP' t1 l2)) = ((term10 _25719 _25727 ZIP' h1' t1 l2) = (term12 _25719 _25727 h1' ZIP' t1 l2)).
Proof. exact (MK_COMB (@lem1108382 _25719 _25727 ZIP' h1' t1 l2) (@lem1108381 _25719 _25727 h1' ZIP' t1 l2)). Qed.
Lemma lem1108384 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : (term10 _25719 _25727 ZIP' h1' t1 l2) = (term12 _25719 _25727 h1' ZIP' t1 l2).
Proof. exact (EQ_MP (@lem1108383 _25719 _25727 h1' ZIP' t1 l2) (@lem1108380 _25719 _25727 h1' t1 l2 ZIP' h1)). Qed.
Lemma lem1108385 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : term14 _25719 _25727 h1' ZIP' t1.
Proof. exact (fun l2 : list _25727 => @lem1108384 _25719 _25727 h1' t1 l2 ZIP' h1). Qed.
Lemma lem1108386 {_25719 _25727 : Type'} (h1' : _25719) (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : term15 _25719 _25727 h1' ZIP'.
Proof. exact (fun t1 : list _25719 => @lem1108385 _25719 _25727 h1' t1 ZIP' h1). Qed.
Lemma lem1108387 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term4 _25719 _25727 ZIP') : term16 _25719 _25727 ZIP'.
Proof. exact (fun h1' : _25719 => @lem1108386 _25719 _25727 h1' ZIP' h1). Qed.
Lemma lem1108388 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term17 _25719 _25727 ZIP'.
Proof. exact (h1). Qed.
Lemma lem1108389 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term4 _25719 _25727 ZIP'.
Proof. exact (proj2 (@lem1108388 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108390 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : (ZIP' (@nil _25719)) = (term0 _25719 _25727).
Proof. exact (proj1 (@lem1108388 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108391 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : ((ZIP' (@nil _25719)) = (term0 _25719 _25727)) = (term3 _25719 _25727 ZIP').
Proof. exact (prop_ext (fun h2 : (ZIP' (@nil _25719)) = (term0 _25719 _25727) => @lem1108371 _25719 _25727 ZIP' h2) (fun h2 : term3 _25719 _25727 ZIP' => @lem1108390 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108392 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term3 _25719 _25727 ZIP'.
Proof. exact (EQ_MP (@lem1108391 _25719 _25727 ZIP' h1) (@lem1108390 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108393 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : (term4 _25719 _25727 ZIP') = (term16 _25719 _25727 ZIP').
Proof. exact (prop_ext (fun h2 : term4 _25719 _25727 ZIP' => @lem1108387 _25719 _25727 ZIP' h2) (fun h2 : term16 _25719 _25727 ZIP' => @lem1108389 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108394 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term16 _25719 _25727 ZIP'.
Proof. exact (EQ_MP (@lem1108393 _25719 _25727 ZIP' h1) (@lem1108389 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108395 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term18 _25719 _25727 ZIP'.
Proof. exact (conj (@lem1108392 _25719 _25727 ZIP' h1) (@lem1108394 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108396 {A Z : Type'} (NIL' : Z) : term19 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1108397 {A Z : Type'} (NIL' : Z) : (term19 A Z NIL') = (term20 A Z NIL').
Proof. exact (eq_refl (term19 A Z NIL')). Qed.
Lemma lem1108398 {A Z : Type'} (NIL' : Z) : term20 A Z NIL'.
Proof. exact (EQ_MP (@lem1108397 A Z NIL') (@lem1108396 A Z NIL')). Qed.
Lemma lem1108399 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term21 A Z NIL' CONS'.
Proof. exact (@lem1108398 A Z NIL' CONS'). Qed.
Lemma lem1108400 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term21 A Z NIL' CONS') = (term22 A Z NIL' CONS').
Proof. exact (eq_refl (term21 A Z NIL' CONS')). Qed.
Lemma lem1108401 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term22 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1108400 A Z NIL' CONS') (@lem1108399 A Z NIL' CONS')). Qed.
Lemma lem1108402 {_25719 _25727 : Type'} (NIL' : type1153 _25719 _25727) (CONS' : type1389 _25719 _25727) : term23 _25719 _25727 NIL' CONS'.
Proof. exact (@lem1108401 _25719 (type1153 _25719 _25727) NIL' CONS'). Qed.
Lemma lem1108403 {_25719 _25727 : Type'} : term24 _25719 _25727.
Proof. exact (@lem1108402 _25719 _25727 (term0 _25719 _25727) (term25 _25719 _25727)). Qed.
Lemma lem1108404 {_25719 _25727 : Type'} (a0 : _25719) : (term26 _25719 _25727 a0) = (term27 _25719 _25727 a0).
Proof. exact (eq_refl (term26 _25719 _25727 a0)). Qed.
Lemma lem1108405 {_25719 : Type'} (a1 : list _25719) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1108406 {_25719 _25727 : Type'} (a0 : _25719) (a1 : list _25719) : (term28 _25719 _25727 a0 a1) = (term29 _25719 _25727 a0 a1).
Proof. exact (MK_COMB (@lem1108404 _25719 _25727 a0) (@lem1108405 _25719 a1)). Qed.
Lemma lem1108407 {_25719 _25727 : Type'} (a1 : list _25719) (a0 : _25719) : (term29 _25719 _25727 a0 a1) = (term30 _25719 _25727 a0).
Proof. exact (eq_refl (term29 _25719 _25727 a0 a1)). Qed.
Lemma lem1108408 {_25719 _25727 : Type'} (a1 : list _25719) (a0 : _25719) : (term28 _25719 _25727 a0 a1) = (term30 _25719 _25727 a0).
Proof. exact (TRANS (@lem1108406 _25719 _25727 a0 a1) (@lem1108407 _25719 _25727 a1 a0)). Qed.
Lemma lem1108409 {_25719 _25727 : Type'} (fn : type1134 _25719 _25727) (a1 : list _25719) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1108410 {_25719 _25727 : Type'} (a0 : _25719) (fn : type1134 _25719 _25727) (a1 : list _25719) : (term31 _25719 _25727 a0 fn a1) = (term32 _25719 _25727 a0 fn a1).
Proof. exact (MK_COMB (@lem1108408 _25719 _25727 a1 a0) (@lem1108409 _25719 _25727 fn a1)). Qed.
Lemma lem1108411 {_25719 _25727 : Type'} (a0 : _25719) (fn : type1134 _25719 _25727) (a1 : list _25719) : (term32 _25719 _25727 a0 fn a1) = (term9 _25719 _25727 a0 fn a1).
Proof. exact (eq_refl (term32 _25719 _25727 a0 fn a1)). Qed.
Lemma lem1108412 {_25719 _25727 : Type'} (a0 : _25719) (fn : type1134 _25719 _25727) (a1 : list _25719) : (term31 _25719 _25727 a0 fn a1) = (term9 _25719 _25727 a0 fn a1).
Proof. exact (TRANS (@lem1108410 _25719 _25727 a0 fn a1) (@lem1108411 _25719 _25727 a0 fn a1)). Qed.
Lemma lem1108413 {_25719 _25727 : Type'} (fn : type1134 _25719 _25727) (a0 : _25719) (a1 : list _25719) : (term33 _25719 _25727 fn a0 a1) = (term33 _25719 _25727 fn a0 a1).
Proof. exact (eq_refl (term33 _25719 _25727 fn a0 a1)). Qed.
Lemma lem1108414 {_25719 _25727 : Type'} (a0 : _25719) (fn : type1134 _25719 _25727) (a1 : list _25719) : ((term8 _25719 _25727 fn a0 a1) = (term31 _25719 _25727 a0 fn a1)) = ((term8 _25719 _25727 fn a0 a1) = (term9 _25719 _25727 a0 fn a1)).
Proof. exact (MK_COMB (@lem1108413 _25719 _25727 fn a0 a1) (@lem1108412 _25719 _25727 a0 fn a1)). Qed.
Lemma lem1108415 {_25719 _25727 : Type'} (a0 : _25719) (fn : type1134 _25719 _25727) : (term34 _25719 _25727 a0 fn) = (term35 _25719 _25727 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25719 => @lem1108414 _25719 _25727 a0 fn a1)). Qed.
Lemma lem1108416 {_25719 : Type'} : (@all (list _25719)) = (@all (list _25719)).
Proof. exact (eq_refl (@all (list _25719))). Qed.
Lemma lem1108417 {_25719 _25727 : Type'} (a0 : _25719) (fn : type1134 _25719 _25727) : (term36 _25719 _25727 a0 fn) = (term6 _25719 _25727 a0 fn).
Proof. exact (MK_COMB (@lem1108416 _25719) (@lem1108415 _25719 _25727 a0 fn)). Qed.
Lemma lem1108418 {_25719 _25727 : Type'} (fn : type1134 _25719 _25727) : (term37 _25719 _25727 fn) = (term38 _25719 _25727 fn).
Proof. exact (fun_ext (fun a0 : _25719 => @lem1108417 _25719 _25727 a0 fn)). Qed.
Lemma lem1108419 {_25719 : Type'} : (@all _25719) = (@all _25719).
Proof. exact (eq_refl (@all _25719)). Qed.
Lemma lem1108420 {_25719 _25727 : Type'} (fn : type1134 _25719 _25727) : (term39 _25719 _25727 fn) = (term4 _25719 _25727 fn).
Proof. exact (MK_COMB (@lem1108419 _25719) (@lem1108418 _25719 _25727 fn)). Qed.
Lemma lem1108421 {_25719 _25727 : Type'} (fn : type1134 _25719 _25727) : (term40 _25719 _25727 fn) = (term40 _25719 _25727 fn).
Proof. exact (eq_refl (term40 _25719 _25727 fn)). Qed.
Lemma lem1108422 {_25719 _25727 : Type'} (fn : type1134 _25719 _25727) : (term41 _25719 _25727 fn) = (term17 _25719 _25727 fn).
Proof. exact (MK_COMB (@lem1108421 _25719 _25727 fn) (@lem1108420 _25719 _25727 fn)). Qed.
Lemma lem1108423 {_25719 _25727 : Type'} : (term42 _25719 _25727) = (term43 _25719 _25727).
Proof. exact (fun_ext (fun fn : type1134 _25719 _25727 => @lem1108422 _25719 _25727 fn)). Qed.
Lemma lem1108424 {_25719 _25727 : Type'} : (@ex ((list _25719) -> (list _25727) -> list (prod _25719 _25727))) = (@ex ((list _25719) -> (list _25727) -> list (prod _25719 _25727))).
Proof. exact (eq_refl (@ex ((list _25719) -> (list _25727) -> list (prod _25719 _25727)))). Qed.
Lemma lem1108425 {_25719 _25727 : Type'} : (term24 _25719 _25727) = (term44 _25719 _25727).
Proof. exact (MK_COMB (@lem1108424 _25719 _25727) (@lem1108423 _25719 _25727)). Qed.
Lemma lem1108426 {_25719 _25727 : Type'} : term44 _25719 _25727.
Proof. exact (EQ_MP (@lem1108425 _25719 _25727) (@lem1108403 _25719 _25727)). Qed.
Lemma lem1108427 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term17 _25719 _25727 ZIP'.
Proof. exact (h1). Qed.
Lemma lem1108428 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term4 _25719 _25727 ZIP'.
Proof. exact (proj2 (@lem1108427 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108429 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : (ZIP' (@nil _25719)) = (term0 _25719 _25727).
Proof. exact (proj1 (@lem1108427 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108430 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term17 _25719 _25727 ZIP'.
Proof. exact (conj (@lem1108429 _25719 _25727 ZIP' h1) (@lem1108428 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108431 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term44 _25719 _25727.
Proof. exact (ex_intro (term43 _25719 _25727) ZIP' (@lem1108430 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108432 {_25719 _25727 : Type'} (h1 : term44 _25719 _25727) : term44 _25719 _25727.
Proof. exact (h1). Qed.
Lemma lem1108433 {_25719 _25727 : Type'} (h1 : term44 _25719 _25727) : term44 _25719 _25727.
Proof. exact (ex_elim (@lem1108432 _25719 _25727 h1) (fun ZIP' : type1134 _25719 _25727 => fun h0 : term43 _25719 _25727 ZIP' => @lem1108431 _25719 _25727 ZIP' h0)). Qed.
Lemma lem1108434 {_25719 _25727 : Type'} : (term44 _25719 _25727) = (term44 _25719 _25727).
Proof. exact (prop_ext (fun h1 : term44 _25719 _25727 => @lem1108433 _25719 _25727 h1) (fun h1 : term44 _25719 _25727 => @lem1108426 _25719 _25727)). Qed.
Lemma lem1108435 {_25719 _25727 : Type'} : term44 _25719 _25727.
Proof. exact (EQ_MP (@lem1108434 _25719 _25727) (@lem1108426 _25719 _25727)). Qed.
Lemma lem1108436 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term17 _25719 _25727 ZIP') : term45 _25719 _25727.
Proof. exact (ex_intro (term46 _25719 _25727) ZIP' (@lem1108395 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108437 {_25719 _25727 : Type'} (h1 : term44 _25719 _25727) : term44 _25719 _25727.
Proof. exact (h1). Qed.
Lemma lem1108438 {_25719 _25727 : Type'} (h1 : term44 _25719 _25727) : term45 _25719 _25727.
Proof. exact (ex_elim (@lem1108437 _25719 _25727 h1) (fun ZIP' : type1134 _25719 _25727 => fun h0 : term43 _25719 _25727 ZIP' => @lem1108436 _25719 _25727 ZIP' h0)). Qed.
Lemma lem1108439 {_25719 _25727 : Type'} : (term44 _25719 _25727) = (term45 _25719 _25727).
Proof. exact (prop_ext (fun h1 : term44 _25719 _25727 => @lem1108438 _25719 _25727 h1) (fun h1 : term45 _25719 _25727 => @lem1108435 _25719 _25727)). Qed.
Lemma lem1108440 {_25719 _25727 : Type'} : term45 _25719 _25727.
Proof. exact (EQ_MP (@lem1108439 _25719 _25727) (@lem1108435 _25719 _25727)). Qed.
Lemma lem1108443 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term18 _25719 _25727 ZIP') : term18 _25719 _25727 ZIP'.
Proof. exact (h1). Qed.
Lemma lem1108444 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) (h1 : term18 _25719 _25727 ZIP') : term45 _25719 _25727.
Proof. exact (ex_intro (term46 _25719 _25727) ZIP' (@lem1108443 _25719 _25727 ZIP' h1)). Qed.
Lemma lem1108445 {_25719 _25727 : Type'} (h1 : term45 _25719 _25727) : term45 _25719 _25727.
Proof. exact (h1). Qed.
Lemma lem1108446 {_25719 _25727 : Type'} (h1 : term45 _25719 _25727) : term45 _25719 _25727.
Proof. exact (ex_elim (@lem1108445 _25719 _25727 h1) (fun ZIP' : type1134 _25719 _25727 => fun h0 : term46 _25719 _25727 ZIP' => @lem1108444 _25719 _25727 ZIP' h0)). Qed.
Lemma lem1108447 {_25719 _25727 : Type'} : (term45 _25719 _25727) = (term45 _25719 _25727).
Proof. exact (prop_ext (fun h1 : term45 _25719 _25727 => @lem1108446 _25719 _25727 h1) (fun h1 : term45 _25719 _25727 => @lem1108440 _25719 _25727)). Qed.
Lemma lem1108448 {_25719 _25727 : Type'} : term45 _25719 _25727.
Proof. exact (EQ_MP (@lem1108447 _25719 _25727) (@lem1108440 _25719 _25727)). Qed.
Lemma lem1108449 {_25719 _25727 : Type'} : term47 _25719 _25727.
Proof. exact (fun _18042 : type1674 => @lem1108448 _25719 _25727). Qed.
Lemma lem1108450 {A B : Type'} (P : type1413 A B) : term48 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1108451 {A B : Type'} (P : type1413 A B) : (term48 A B P) = ((term49 A B P) = (term50 A B P)).
Proof. exact (eq_refl (term48 A B P)). Qed.
Lemma lem1108454 {A B : Type'} (P : type1413 A B) : (term49 A B P) = (term50 A B P).
Proof. exact (EQ_MP (@lem1108451 A B P) (@lem1108450 A B P)). Qed.
Lemma lem1108455 {_25719 _25727 : Type'} (P : type1295 _25719 _25727) : (term51 _25719 _25727 P) = (term52 _25719 _25727 P).
Proof. exact (@lem1108454 type1674 (type1134 _25719 _25727) P). Qed.
Lemma lem1108456 {_25719 _25727 : Type'} : (term53 _25719 _25727) = (term54 _25719 _25727).
Proof. exact (@lem1108455 _25719 _25727 (term55 _25719 _25727)). Qed.
Lemma lem1108457 {_25719 _25727 : Type'} (_18042 : type1674) : (term56 _25719 _25727 _18042) = (term46 _25719 _25727).
Proof. exact (eq_refl (term56 _25719 _25727 _18042)). Qed.
Lemma lem1108458 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) : ZIP' = ZIP'.
Proof. exact (eq_refl ZIP'). Qed.
Lemma lem1108459 {_25719 _25727 : Type'} (_18042 : type1674) (ZIP' : type1134 _25719 _25727) : (term57 _25719 _25727 _18042 ZIP') = (term58 _25719 _25727 ZIP').
Proof. exact (MK_COMB (@lem1108457 _25719 _25727 _18042) (@lem1108458 _25719 _25727 ZIP')). Qed.
Lemma lem1108460 {_25719 _25727 : Type'} (ZIP' : type1134 _25719 _25727) : (term58 _25719 _25727 ZIP') = (term18 _25719 _25727 ZIP').
Proof. exact (eq_refl (term58 _25719 _25727 ZIP')). Qed.
Lemma lem1108461 {_25719 _25727 : Type'} (_18042 : type1674) (ZIP' : type1134 _25719 _25727) : (term57 _25719 _25727 _18042 ZIP') = (term18 _25719 _25727 ZIP').
Proof. exact (TRANS (@lem1108459 _25719 _25727 _18042 ZIP') (@lem1108460 _25719 _25727 ZIP')). Qed.
Lemma lem1108462 {_25719 _25727 : Type'} (_18042 : type1674) : (term59 _25719 _25727 _18042) = (term46 _25719 _25727).
Proof. exact (fun_ext (fun ZIP' : type1134 _25719 _25727 => @lem1108461 _25719 _25727 _18042 ZIP')). Qed.
Lemma lem1108463 {_25719 _25727 : Type'} : (@ex ((list _25719) -> (list _25727) -> list (prod _25719 _25727))) = (@ex ((list _25719) -> (list _25727) -> list (prod _25719 _25727))).
Proof. exact (eq_refl (@ex ((list _25719) -> (list _25727) -> list (prod _25719 _25727)))). Qed.
Lemma lem1108464 {_25719 _25727 : Type'} (_18042 : type1674) : (term60 _25719 _25727 _18042) = (term45 _25719 _25727).
Proof. exact (MK_COMB (@lem1108463 _25719 _25727) (@lem1108462 _25719 _25727 _18042)). Qed.
Lemma lem1108465 {_25719 _25727 : Type'} : (term61 _25719 _25727) = (term62 _25719 _25727).
Proof. exact (fun_ext (fun _18042 : type1674 => @lem1108464 _25719 _25727 _18042)). Qed.
Lemma lem1108466 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1108467 {_25719 _25727 : Type'} : (term53 _25719 _25727) = (term47 _25719 _25727).
Proof. exact (MK_COMB (@lem1108466) (@lem1108465 _25719 _25727)). Qed.
Lemma lem1108468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1108469 {_25719 _25727 : Type'} : (term63 _25719 _25727) = (term64 _25719 _25727).
Proof. exact (MK_COMB (@lem1108468) (@lem1108467 _25719 _25727)). Qed.
Lemma lem1108470 {_25719 _25727 : Type'} (_18042 : type1674) : (term56 _25719 _25727 _18042) = (term46 _25719 _25727).
Proof. exact (eq_refl (term56 _25719 _25727 _18042)). Qed.
Lemma lem1108471 {_25719 _25727 : Type'} (ZIP' : type1303 _25719 _25727) (_18042 : type1674) : (ZIP' _18042) = (ZIP' _18042).
Proof. exact (eq_refl (ZIP' _18042)). Qed.
Lemma lem1108472 {_25719 _25727 : Type'} (ZIP' : type1303 _25719 _25727) (_18042 : type1674) : (term65 _25719 _25727 ZIP' _18042) = (term66 _25719 _25727 ZIP' _18042).
Proof. exact (MK_COMB (@lem1108470 _25719 _25727 _18042) (@lem1108471 _25719 _25727 ZIP' _18042)). Qed.
Lemma lem1108473 {_25719 _25727 : Type'} (ZIP' : type1303 _25719 _25727) (_18042 : type1674) : (term66 _25719 _25727 ZIP' _18042) = (term67 _25719 _25727 ZIP' _18042).
Proof. exact (eq_refl (term66 _25719 _25727 ZIP' _18042)). Qed.
Lemma lem1108474 {_25719 _25727 : Type'} (ZIP' : type1303 _25719 _25727) (_18042 : type1674) : (term65 _25719 _25727 ZIP' _18042) = (term67 _25719 _25727 ZIP' _18042).
Proof. exact (TRANS (@lem1108472 _25719 _25727 ZIP' _18042) (@lem1108473 _25719 _25727 ZIP' _18042)). Qed.
Lemma lem1108475 {_25719 _25727 : Type'} (ZIP' : type1303 _25719 _25727) : (term68 _25719 _25727 ZIP') = (term69 _25719 _25727 ZIP').
Proof. exact (fun_ext (fun _18042 : type1674 => @lem1108474 _25719 _25727 ZIP' _18042)). Qed.
Lemma lem1108476 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem1108477 {_25719 _25727 : Type'} (ZIP' : type1303 _25719 _25727) : (term70 _25719 _25727 ZIP') = (term71 _25719 _25727 ZIP').
Proof. exact (MK_COMB (@lem1108476) (@lem1108475 _25719 _25727 ZIP')). Qed.
Lemma lem1108478 {_25719 _25727 : Type'} : (term72 _25719 _25727) = (term73 _25719 _25727).
Proof. exact (fun_ext (fun ZIP' : type1303 _25719 _25727 => @lem1108477 _25719 _25727 ZIP')). Qed.
Lemma lem1108479 {_25719 _25727 : Type'} : (@ex ((prod nat (prod nat nat)) -> (list _25719) -> (list _25727) -> list (prod _25719 _25727))) = (@ex ((prod nat (prod nat nat)) -> (list _25719) -> (list _25727) -> list (prod _25719 _25727))).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> (list _25719) -> (list _25727) -> list (prod _25719 _25727)))). Qed.
Lemma lem1108480 {_25719 _25727 : Type'} : (term54 _25719 _25727) = (term74 _25719 _25727).
Proof. exact (MK_COMB (@lem1108479 _25719 _25727) (@lem1108478 _25719 _25727)). Qed.
Lemma lem1108481 {_25719 _25727 : Type'} : ((term53 _25719 _25727) = (term54 _25719 _25727)) = ((term47 _25719 _25727) = (term74 _25719 _25727)).
Proof. exact (MK_COMB (@lem1108469 _25719 _25727) (@lem1108480 _25719 _25727)). Qed.
Lemma lem1108482 {_25719 _25727 : Type'} : (term47 _25719 _25727) = (term74 _25719 _25727).
Proof. exact (EQ_MP (@lem1108481 _25719 _25727) (@lem1108456 _25719 _25727)). Qed.
Lemma lem1108483 {_25719 _25727 : Type'} : term74 _25719 _25727.
Proof. exact (EQ_MP (@lem1108482 _25719 _25727) (@lem1108449 _25719 _25727)). Qed.
Lemma lem1108485 {A : Type'} : (@ex A) = (term75 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1108486 {_25719 _25727 : Type'} : (@ex ((prod nat (prod nat nat)) -> (list _25719) -> (list _25727) -> list (prod _25719 _25727))) = (term76 _25719 _25727).
Proof. exact (@lem1108485 (type1303 _25719 _25727)). Qed.
Lemma lem1108487 {_25719 _25727 : Type'} : (term73 _25719 _25727) = (term73 _25719 _25727).
Proof. exact (eq_refl (term73 _25719 _25727)). Qed.
Lemma lem1108488 {_25719 _25727 : Type'} : (term74 _25719 _25727) = (term77 _25719 _25727).
Proof. exact (MK_COMB (@lem1108486 _25719 _25727) (@lem1108487 _25719 _25727)). Qed.
Lemma lem1108489 {_25719 _25727 : Type'} : (term77 _25719 _25727) = (term78 _25719 _25727).
Proof. exact (eq_refl (term77 _25719 _25727)). Qed.
Lemma lem1108490 {_25719 _25727 : Type'} : (term74 _25719 _25727) = (term78 _25719 _25727).
Proof. exact (TRANS (@lem1108488 _25719 _25727) (@lem1108489 _25719 _25727)). Qed.
Lemma lem1108491 {_25719 _25727 : Type'} : term78 _25719 _25727.
Proof. exact (EQ_MP (@lem1108490 _25719 _25727) (@lem1108483 _25719 _25727)). Qed.
