Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931456_term_abbrevs.
Require Import thm32_spec.
Require Import tybit1_RECURSION_spec.
Lemma lem7931388 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term0 A _103819.
Proof. exact (h1). Qed.
Lemma lem7931389 {A : Type'} (a : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : term1 A _103819 a.
Proof. exact (@lem7931388 A _103819 h1 a). Qed.
Lemma lem7931390 {A : Type'} (_103819 : type1348 A) (a : type6 A) : (term1 A _103819 a) = ((term2 A _103819 a) = a).
Proof. exact (eq_refl (term1 A _103819 a)). Qed.
Lemma lem7931391 {A : Type'} (a : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : (term2 A _103819 a) = a.
Proof. exact (EQ_MP (@lem7931390 A _103819 a) (@lem7931389 A a _103819 h1)). Qed.
Lemma lem7931392 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term0 A _103819.
Proof. exact (fun a : type6 A => @lem7931391 A a _103819 h1). Qed.
Lemma lem7931393 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term0 A _103819.
Proof. exact (h1). Qed.
Lemma lem7931394 {A : Type'} (_103819 : type1348 A) : (term0 A _103819) = (term0 A _103819).
Proof. exact (prop_ext (fun h1 : term0 A _103819 => @lem7931392 A _103819 h1) (fun h1 : term0 A _103819 => @lem7931393 A _103819 h1)). Qed.
Lemma lem7931395 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term0 A _103819.
Proof. exact (EQ_MP (@lem7931394 A _103819) (@lem7931393 A _103819 h1)). Qed.
Lemma lem7931396 {A Z : Type'} (f : type41 A Z) : term3 A Z f.
Proof. exact (@lem7931326 A Z f). Qed.
Lemma lem7931397 {A Z : Type'} (f : type41 A Z) : (term3 A Z f) = (term4 A Z f).
Proof. exact (eq_refl (term3 A Z f)). Qed.
Lemma lem7931398 {A Z : Type'} (f : type41 A Z) : term4 A Z f.
Proof. exact (EQ_MP (@lem7931397 A Z f) (@lem7931396 A Z f)). Qed.
Lemma lem7931399 {A : Type'} (f : type37 A) : term5 A f.
Proof. exact (@lem7931398 A (type6 A) f). Qed.
Lemma lem7931400 {A : Type'} : term6 A.
Proof. exact (@lem7931399 A (term7 A)). Qed.
Lemma lem7931401 {A : Type'} (a : type6 A) : (term8 A a) = a.
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem7931402 {A : Type'} (fn : type1348 A) (a : type6 A) : (term9 A fn a) = (term9 A fn a).
Proof. exact (eq_refl (term9 A fn a)). Qed.
Lemma lem7931403 {A : Type'} (fn : type1348 A) (a : type6 A) : ((term2 A fn a) = (term8 A a)) = ((term2 A fn a) = a).
Proof. exact (MK_COMB (@lem7931402 A fn a) (@lem7931401 A a)). Qed.
Lemma lem7931404 {A : Type'} (fn : type1348 A) : (term10 A fn) = (term11 A fn).
Proof. exact (fun_ext (fun a : type6 A => @lem7931403 A fn a)). Qed.
Lemma lem7931405 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7931406 {A : Type'} (fn : type1348 A) : (term12 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem7931405 A) (@lem7931404 A fn)). Qed.
Lemma lem7931407 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun fn : type1348 A => @lem7931406 A fn)). Qed.
Lemma lem7931408 {A : Type'} : (@ex ((tybit1 A) -> finite_sum (finite_sum A A) unit)) = (@ex ((tybit1 A) -> finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@ex ((tybit1 A) -> finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7931409 {A : Type'} : (term6 A) = (term15 A).
Proof. exact (MK_COMB (@lem7931408 A) (@lem7931407 A)). Qed.
Lemma lem7931410 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7931409 A) (@lem7931400 A)). Qed.
Lemma lem7931411 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term0 A _103819.
Proof. exact (h1). Qed.
Lemma lem7931412 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term15 A.
Proof. exact (ex_intro (term14 A) _103819 (@lem7931411 A _103819 h1)). Qed.
Lemma lem7931413 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7931414 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (ex_elim (@lem7931413 A h1) (fun _103819 : type1348 A => fun h0 : term14 A _103819 => @lem7931412 A _103819 h0)). Qed.
Lemma lem7931415 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7931414 A h1) (fun h1 : term15 A => @lem7931410 A)). Qed.
Lemma lem7931416 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7931415 A) (@lem7931410 A)). Qed.
Lemma lem7931417 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term15 A.
Proof. exact (ex_intro (term14 A) _103819 (@lem7931395 A _103819 h1)). Qed.
Lemma lem7931418 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7931419 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (ex_elim (@lem7931418 A h1) (fun _103819 : type1348 A => fun h0 : term14 A _103819 => @lem7931417 A _103819 h0)). Qed.
Lemma lem7931420 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7931419 A h1) (fun h1 : term15 A => @lem7931416 A)). Qed.
Lemma lem7931421 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7931420 A) (@lem7931416 A)). Qed.
Lemma lem7931424 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term0 A _103819.
Proof. exact (h1). Qed.
Lemma lem7931425 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term15 A.
Proof. exact (ex_intro (term14 A) _103819 (@lem7931424 A _103819 h1)). Qed.
Lemma lem7931426 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7931427 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (ex_elim (@lem7931426 A h1) (fun _103819 : type1348 A => fun h0 : term14 A _103819 => @lem7931425 A _103819 h0)). Qed.
Lemma lem7931428 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7931427 A h1) (fun h1 : term15 A => @lem7931421 A)). Qed.
Lemma lem7931429 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem7931428 A) (@lem7931421 A)). Qed.
Lemma lem7931430 {A : Type'} (a : type6 A) (a' : type6 A) (h1 : (@mktybit1 A a) = (@mktybit1 A a')) : (@mktybit1 A a) = (@mktybit1 A a').
Proof. exact (h1). Qed.
Lemma lem7931431 {A : Type'} (_103819 : type1348 A) : _103819 = _103819.
Proof. exact (eq_refl _103819). Qed.
Lemma lem7931432 {A : Type'} (_103819 : type1348 A) (a : type6 A) (a' : type6 A) (h1 : (@mktybit1 A a) = (@mktybit1 A a')) : (term2 A _103819 a) = (term2 A _103819 a').
Proof. exact (MK_COMB (@lem7931431 A _103819) (@lem7931430 A a a' h1)). Qed.
Lemma lem7931433 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term0 A _103819.
Proof. exact (h1). Qed.
Lemma lem7931434 {A : Type'} (a : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : term1 A _103819 a.
Proof. exact (@lem7931433 A _103819 h1 a). Qed.
Lemma lem7931435 {A : Type'} (_103819 : type1348 A) (a : type6 A) : (term1 A _103819 a) = ((term2 A _103819 a) = a).
Proof. exact (eq_refl (term1 A _103819 a)). Qed.
Lemma lem7931436 {A : Type'} (a : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : (term2 A _103819 a) = a.
Proof. exact (EQ_MP (@lem7931435 A _103819 a) (@lem7931434 A a _103819 h1)). Qed.
Lemma lem7931437 {A : Type'} (a' : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : (term2 A _103819 a') = a'.
Proof. exact (@lem7931436 A a' _103819 h1). Qed.
Lemma lem7931438 {A : Type'} (a : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : a = (term2 A _103819 a).
Proof. exact (SYM (@lem7931436 A a _103819 h1)). Qed.
Lemma lem7931439 {A : Type'} (_103819 : type1348 A) (a : type6 A) (a' : type6 A) (h1 : term0 A _103819) (h2 : (@mktybit1 A a) = (@mktybit1 A a')) : a = (term2 A _103819 a').
Proof. exact (TRANS (@lem7931438 A a _103819 h1) (@lem7931432 A _103819 a a' h2)). Qed.
Lemma lem7931442 {A : Type'} (_103819 : type1348 A) (a : type6 A) (a' : type6 A) (h1 : term0 A _103819) (h2 : (@mktybit1 A a) = (@mktybit1 A a')) : a = a'.
Proof. exact (TRANS (@lem7931439 A _103819 a a' h1 h2) (@lem7931437 A a' _103819 h1)). Qed.
Lemma lem7931443 {A : Type'} : (@mktybit1 A) = (@mktybit1 A).
Proof. exact (eq_refl (@mktybit1 A)). Qed.
Lemma lem7931444 {A : Type'} (a : type6 A) (a' : type6 A) (h1 : a = a') : a = a'.
Proof. exact (h1). Qed.
Lemma lem7931445 {A : Type'} (a : type6 A) (a' : type6 A) (h1 : a = a') : (@mktybit1 A a) = (@mktybit1 A a').
Proof. exact (MK_COMB (@lem7931443 A) (@lem7931444 A a a' h1)). Qed.
Lemma lem7931446 {A : Type'} (a : type6 A) (a' : type6 A) : term16 A a a'.
Proof. exact (fun h0 : a = a' => @lem7931445 A a a' h0). Qed.
Lemma lem7931447 {A : Type'} (a : type6 A) (a' : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : term17 A a a'.
Proof. exact (fun h0 : (@mktybit1 A a) = (@mktybit1 A a') => @lem7931442 A _103819 a a' h1 h0). Qed.
Lemma lem7931448 {A : Type'} (a : type6 A) (a' : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : term18 A a a'.
Proof. exact (conj (@lem7931447 A a a' _103819 h1) (@lem7931446 A a a')). Qed.
Lemma lem7931449 {A : Type'} (a : type6 A) (a' : type6 A) : (term18 A a a') = (((@mktybit1 A a) = (@mktybit1 A a')) = (a = a')).
Proof. exact (@lem32 ((@mktybit1 A a) = (@mktybit1 A a')) (a = a')). Qed.
Lemma lem7931450 {A : Type'} (a : type6 A) (a' : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : ((@mktybit1 A a) = (@mktybit1 A a')) = (a = a').
Proof. exact (EQ_MP (@lem7931449 A a a') (@lem7931448 A a a' _103819 h1)). Qed.
Lemma lem7931451 {A : Type'} (a : type6 A) (_103819 : type1348 A) (h1 : term0 A _103819) : term19 A a.
Proof. exact (fun a' : type6 A => @lem7931450 A a a' _103819 h1). Qed.
Lemma lem7931452 {A : Type'} (_103819 : type1348 A) (h1 : term0 A _103819) : term20 A.
Proof. exact (fun a : type6 A => @lem7931451 A a _103819 h1). Qed.
Lemma lem7931453 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem7931454 {A : Type'} (h1 : term15 A) : term20 A.
Proof. exact (ex_elim (@lem7931453 A h1) (fun _103819 : type1348 A => fun h0 : term14 A _103819 => @lem7931452 A _103819 h0)). Qed.
Lemma lem7931455 {A : Type'} : (term15 A) = (term20 A).
Proof. exact (prop_ext (fun h1 : term15 A => @lem7931454 A h1) (fun h1 : term20 A => @lem7931429 A)). Qed.
Lemma lem7931456 {A : Type'} : term20 A.
Proof. exact (EQ_MP (@lem7931455 A) (@lem7931429 A)). Qed.
