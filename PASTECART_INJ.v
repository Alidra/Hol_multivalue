Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PASTECART_INJ_term_abbrevs.
Require Import FSTCART_PASTECART_spec.
Require Import PASTECART_EQ_spec.
Require Import SNDCART_PASTECART_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem7664354 {A M N : Type'} (x : cart A M) : term0 A M N x.
Proof. exact (@lem7648197 A M N x). Qed.
Lemma lem7664355 {A M N : Type'} (x : cart A M) : (term0 A M N x) = (term1 A M N x).
Proof. exact (eq_refl (term0 A M N x)). Qed.
Lemma lem7664356 {A M N : Type'} (x : cart A M) : term1 A M N x.
Proof. exact (EQ_MP (@lem7664355 A M N x) (@lem7664354 A M N x)). Qed.
Lemma lem7664357 {A M N : Type'} (x : cart A M) (y : cart A N) : term2 A M N x y.
Proof. exact (@lem7664356 A M N x y). Qed.
Lemma lem7664358 {A M N : Type'} (x : cart A M) (y : cart A N) : (term2 A M N x y) = ((term3 A M N x y) = y).
Proof. exact (eq_refl (term2 A M N x y)). Qed.
Lemma lem7664360 {A M N : Type'} (x : cart A M) : term4 A M N x.
Proof. exact (@lem7643282 A M N x). Qed.
Lemma lem7664361 {A M N : Type'} (x : cart A M) : (term4 A M N x) = (term5 A M N x).
Proof. exact (eq_refl (term4 A M N x)). Qed.
Lemma lem7664362 {A M N : Type'} (x : cart A M) : term5 A M N x.
Proof. exact (EQ_MP (@lem7664361 A M N x) (@lem7664360 A M N x)). Qed.
Lemma lem7664363 {A M N : Type'} (x : cart A M) (y : cart A N) : term6 A M N x y.
Proof. exact (@lem7664362 A M N x y). Qed.
Lemma lem7664364 {A M N : Type'} (y : cart A N) (x : cart A M) : (term6 A M N x y) = ((term7 A M N x y) = x).
Proof. exact (eq_refl (term6 A M N x y)). Qed.
Lemma lem7664366 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) : term8 _140423 _140433 _140434 x.
Proof. exact (@lem7660836 _140423 _140433 _140434 x). Qed.
Lemma lem7664367 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) : (term8 _140423 _140433 _140434 x) = (term9 _140423 _140433 _140434 x).
Proof. exact (eq_refl (term8 _140423 _140433 _140434 x)). Qed.
Lemma lem7664368 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) : term9 _140423 _140433 _140434 x.
Proof. exact (EQ_MP (@lem7664367 _140423 _140433 _140434 x) (@lem7664366 _140423 _140433 _140434 x)). Qed.
Lemma lem7664369 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) (y : type3 _140423 _140433 _140434) : term10 _140423 _140433 _140434 x y.
Proof. exact (@lem7664368 _140423 _140433 _140434 x y). Qed.
Lemma lem7664370 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) (y : type3 _140423 _140433 _140434) : (term10 _140423 _140433 _140434 x y) = ((x = y) = (term11 _140423 _140433 _140434 x y)).
Proof. exact (eq_refl (term10 _140423 _140433 _140434 x y)). Qed.
Lemma lem7664395 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) (y : type3 _140423 _140433 _140434) : (x = y) = (term11 _140423 _140433 _140434 x y).
Proof. exact (EQ_MP (@lem7664370 _140423 _140433 _140434 x y) (@lem7664369 _140423 _140433 _140434 x y)). Qed.
Lemma lem7664396 {A M N : Type'} (x : type2 A M N) (y : type2 A M N) : (x = y) = (term12 A M N x y).
Proof. exact (@lem7664395 M A N x y). Qed.
Lemma lem7664397 {A M N : Type'} (x : cart A M) (y : cart A N) (w : cart A M) (z : cart A N) : ((@pastecart A M N x y) = (@pastecart A M N w z)) = (term13 A M N x y w z).
Proof. exact (@lem7664396 A M N (@pastecart A M N x y) (@pastecart A M N w z)). Qed.
Lemma lem7664405 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (EQ_MP (@lem7664364 A M N y x) (@lem7664363 A M N x y)). Qed.
Lemma lem7664406 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (@lem7664405 A M N y x). Qed.
Lemma lem7664407 {A M : Type'} : (@eq (cart A M)) = (@eq (cart A M)).
Proof. exact (eq_refl (@eq (cart A M))). Qed.
Lemma lem7664408 {A M N : Type'} (y : cart A N) (x : cart A M) : (term14 A M N x y) = (@eq (cart A M) x).
Proof. exact (MK_COMB (@lem7664407 A M) (@lem7664406 A M N y x)). Qed.
Lemma lem7664410 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (EQ_MP (@lem7664364 A M N y x) (@lem7664363 A M N x y)). Qed.
Lemma lem7664411 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (@lem7664410 A M N y x). Qed.
Lemma lem7664412 {A M N : Type'} (z : cart A N) (w : cart A M) : (term7 A M N w z) = w.
Proof. exact (@lem7664411 A M N z w). Qed.
Lemma lem7664413 {A M N : Type'} (y : cart A N) (z : cart A N) (x : cart A M) (w : cart A M) : ((term7 A M N x y) = (term7 A M N w z)) = (x = w).
Proof. exact (MK_COMB (@lem7664408 A M N y x) (@lem7664412 A M N z w)). Qed.
Lemma lem7664418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664419 {A M N : Type'} (y : cart A N) (z : cart A N) (x : cart A M) (w : cart A M) : (term15 A M N x y w z) = (term16 A M x w).
Proof. exact (MK_COMB (@lem7664418) (@lem7664413 A M N y z x w)). Qed.
Lemma lem7664425 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem7664358 A M N x y) (@lem7664357 A M N x y)). Qed.
Lemma lem7664426 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (@lem7664425 A M N x y). Qed.
Lemma lem7664427 {A N : Type'} : (@eq (cart A N)) = (@eq (cart A N)).
Proof. exact (eq_refl (@eq (cart A N))). Qed.
Lemma lem7664428 {A M N : Type'} (x : cart A M) (y : cart A N) : (term17 A M N x y) = (@eq (cart A N) y).
Proof. exact (MK_COMB (@lem7664427 A N) (@lem7664426 A M N x y)). Qed.
Lemma lem7664430 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem7664358 A M N x y) (@lem7664357 A M N x y)). Qed.
Lemma lem7664431 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (@lem7664430 A M N x y). Qed.
Lemma lem7664432 {A M N : Type'} (w : cart A M) (z : cart A N) : (term3 A M N w z) = z.
Proof. exact (@lem7664431 A M N w z). Qed.
Lemma lem7664433 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : ((term3 A M N x y) = (term3 A M N w z)) = (y = z).
Proof. exact (MK_COMB (@lem7664428 A M N x y) (@lem7664432 A M N w z)). Qed.
Lemma lem7664438 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : (term13 A M N x y w z) = (term18 A M N x w y z).
Proof. exact (MK_COMB (@lem7664419 A M N y z x w) (@lem7664433 A M N x w y z)). Qed.
Lemma lem7664441 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : ((@pastecart A M N x y) = (@pastecart A M N w z)) = (term18 A M N x w y z).
Proof. exact (TRANS (@lem7664397 A M N x y w z) (@lem7664438 A M N x w y z)). Qed.
Lemma lem7664442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7664443 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : (term19 A M N x y w z) = (term20 A M N x w y z).
Proof. exact (MK_COMB (@lem7664442) (@lem7664441 A M N x w y z)). Qed.
Lemma lem7664454 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : (term18 A M N x w y z) = (term18 A M N x w y z).
Proof. exact (eq_refl (term18 A M N x w y z)). Qed.
Lemma lem7664455 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : (((@pastecart A M N x y) = (@pastecart A M N w z)) = (term18 A M N x w y z)) = ((term18 A M N x w y z) = (term18 A M N x w y z)).
Proof. exact (MK_COMB (@lem7664443 A M N x w y z) (@lem7664454 A M N x w y z)). Qed.
Lemma lem7664457 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7664458 (x : Prop) : (x = x) = True.
Proof. exact (@lem7664457 Prop x). Qed.
Lemma lem7664459 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : ((term18 A M N x w y z) = (term18 A M N x w y z)) = True.
Proof. exact (@lem7664458 (term18 A M N x w y z)). Qed.
Lemma lem7664460 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : (((@pastecart A M N x y) = (@pastecart A M N w z)) = (term18 A M N x w y z)) = True.
Proof. exact (TRANS (@lem7664455 A M N x w y z) (@lem7664459 A M N x w y z)). Qed.
Lemma lem7664461 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) : (term21 A M N x w y) = (term22 A N).
Proof. exact (fun_ext (fun z : cart A N => @lem7664460 A M N x w y z)). Qed.
Lemma lem7664462 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7664463 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) : (term23 A M N x w y) = (term24 A N).
Proof. exact (MK_COMB (@lem7664462 A N) (@lem7664461 A M N x w y)). Qed.
Lemma lem7664465 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664466 {A N : Type'} (t : Prop) : (term26 A N t) = t.
Proof. exact (@lem7664465 (cart A N) t). Qed.
Lemma lem7664467 {A N : Type'} : (term24 A N) = True.
Proof. exact (@lem7664466 A N True). Qed.
Lemma lem7664468 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) : (term23 A M N x w y) = True.
Proof. exact (TRANS (@lem7664463 A M N x w y) (@lem7664467 A N)). Qed.
Lemma lem7664469 {A M N : Type'} (x : cart A M) (y : cart A N) : (term27 A M N x y) = (term22 A M).
Proof. exact (fun_ext (fun w : cart A M => @lem7664468 A M N x w y)). Qed.
Lemma lem7664470 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem7664471 {A M N : Type'} (x : cart A M) (y : cart A N) : (term28 A M N x y) = (term24 A M).
Proof. exact (MK_COMB (@lem7664470 A M) (@lem7664469 A M N x y)). Qed.
Lemma lem7664473 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664474 {A M : Type'} (t : Prop) : (term26 A M t) = t.
Proof. exact (@lem7664473 (cart A M) t). Qed.
Lemma lem7664475 {A M : Type'} : (term24 A M) = True.
Proof. exact (@lem7664474 A M True). Qed.
Lemma lem7664476 {A M N : Type'} (x : cart A M) (y : cart A N) : (term28 A M N x y) = True.
Proof. exact (TRANS (@lem7664471 A M N x y) (@lem7664475 A M)). Qed.
Lemma lem7664477 {A M N : Type'} (x : cart A M) : (term29 A M N x) = (term22 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem7664476 A M N x y)). Qed.
Lemma lem7664478 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7664479 {A M N : Type'} (x : cart A M) : (term30 A M N x) = (term24 A N).
Proof. exact (MK_COMB (@lem7664478 A N) (@lem7664477 A M N x)). Qed.
Lemma lem7664481 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664482 {A N : Type'} (t : Prop) : (term26 A N t) = t.
Proof. exact (@lem7664481 (cart A N) t). Qed.
Lemma lem7664483 {A N : Type'} : (term24 A N) = True.
Proof. exact (@lem7664482 A N True). Qed.
Lemma lem7664484 {A M N : Type'} (x : cart A M) : (term30 A M N x) = True.
Proof. exact (TRANS (@lem7664479 A M N x) (@lem7664483 A N)). Qed.
Lemma lem7664485 {A M N : Type'} : (term31 A M N) = (term22 A M).
Proof. exact (fun_ext (fun x : cart A M => @lem7664484 A M N x)). Qed.
Lemma lem7664486 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem7664487 {A M N : Type'} : (term32 A M N) = (term24 A M).
Proof. exact (MK_COMB (@lem7664486 A M) (@lem7664485 A M N)). Qed.
Lemma lem7664489 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664490 {A M : Type'} (t : Prop) : (term26 A M t) = t.
Proof. exact (@lem7664489 (cart A M) t). Qed.
Lemma lem7664491 {A M : Type'} : (term24 A M) = True.
Proof. exact (@lem7664490 A M True). Qed.
Lemma lem7664492 {A M N : Type'} : (term32 A M N) = True.
Proof. exact (TRANS (@lem7664487 A M N) (@lem7664491 A M)). Qed.
Lemma lem7664493 {A M N : Type'} : True = (term32 A M N).
Proof. exact (SYM (@lem7664492 A M N)). Qed.
Lemma lem7664494 {A M N : Type'} : term32 A M N.
Proof. exact (EQ_MP (@lem7664493 A M N) (@lem0)). Qed.
