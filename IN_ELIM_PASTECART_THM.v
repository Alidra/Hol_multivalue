Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_ELIM_PASTECART_THM_term_abbrevs.
Require Import FSTCART_PASTECART_spec.
Require Import PASTECART_EQ_spec.
Require Import SNDCART_PASTECART_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Lemma lem8001325 {A M N : Type'} (x : cart A M) : term0 A M N x.
Proof. exact (@lem7648197 A M N x). Qed.
Lemma lem8001326 {A M N : Type'} (x : cart A M) : (term0 A M N x) = (term1 A M N x).
Proof. exact (eq_refl (term0 A M N x)). Qed.
Lemma lem8001327 {A M N : Type'} (x : cart A M) : term1 A M N x.
Proof. exact (EQ_MP (@lem8001326 A M N x) (@lem8001325 A M N x)). Qed.
Lemma lem8001328 {A M N : Type'} (x : cart A M) (y : cart A N) : term2 A M N x y.
Proof. exact (@lem8001327 A M N x y). Qed.
Lemma lem8001329 {A M N : Type'} (x : cart A M) (y : cart A N) : (term2 A M N x y) = ((term3 A M N x y) = y).
Proof. exact (eq_refl (term2 A M N x y)). Qed.
Lemma lem8001331 {A M N : Type'} (x : cart A M) : term4 A M N x.
Proof. exact (@lem7643282 A M N x). Qed.
Lemma lem8001332 {A M N : Type'} (x : cart A M) : (term4 A M N x) = (term5 A M N x).
Proof. exact (eq_refl (term4 A M N x)). Qed.
Lemma lem8001333 {A M N : Type'} (x : cart A M) : term5 A M N x.
Proof. exact (EQ_MP (@lem8001332 A M N x) (@lem8001331 A M N x)). Qed.
Lemma lem8001334 {A M N : Type'} (x : cart A M) (y : cart A N) : term6 A M N x y.
Proof. exact (@lem8001333 A M N x y). Qed.
Lemma lem8001335 {A M N : Type'} (y : cart A N) (x : cart A M) : (term6 A M N x y) = ((term7 A M N x y) = x).
Proof. exact (eq_refl (term6 A M N x y)). Qed.
Lemma lem8001337 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) : term8 _140423 _140433 _140434 x.
Proof. exact (@lem7660836 _140423 _140433 _140434 x). Qed.
Lemma lem8001338 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) : (term8 _140423 _140433 _140434 x) = (term9 _140423 _140433 _140434 x).
Proof. exact (eq_refl (term8 _140423 _140433 _140434 x)). Qed.
Lemma lem8001339 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) : term9 _140423 _140433 _140434 x.
Proof. exact (EQ_MP (@lem8001338 _140423 _140433 _140434 x) (@lem8001337 _140423 _140433 _140434 x)). Qed.
Lemma lem8001340 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) (y : type3 _140423 _140433 _140434) : term10 _140423 _140433 _140434 x y.
Proof. exact (@lem8001339 _140423 _140433 _140434 x y). Qed.
Lemma lem8001341 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) (y : type3 _140423 _140433 _140434) : (term10 _140423 _140433 _140434 x y) = ((x = y) = (term11 _140423 _140433 _140434 x y)).
Proof. exact (eq_refl (term10 _140423 _140433 _140434 x y)). Qed.
Lemma lem8001374 {_83064 : Type'} : term12 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem8001375 {_83064 : Type'} (P : type919 _83064) : term13 _83064 P.
Proof. exact (@lem8001374 _83064 P). Qed.
Lemma lem8001376 {_83064 : Type'} (P : type919 _83064) : (term13 _83064 P) = (term14 _83064 P).
Proof. exact (eq_refl (term13 _83064 P)). Qed.
Lemma lem8001377 {_83064 : Type'} (P : type919 _83064) : term14 _83064 P.
Proof. exact (EQ_MP (@lem8001376 _83064 P) (@lem8001375 _83064 P)). Qed.
Lemma lem8001378 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term15 _83064 P x.
Proof. exact (@lem8001377 _83064 P x). Qed.
Lemma lem8001379 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term15 _83064 P x) = ((term16 _83064 x P) = (term17 _83064 P x)).
Proof. exact (eq_refl (term15 _83064 P x)). Qed.
Lemma lem8001398 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term16 _83064 x P) = (term17 _83064 P x).
Proof. exact (EQ_MP (@lem8001379 _83064 P x) (@lem8001378 _83064 P x)). Qed.
Lemma lem8001399 {_141774 _141775 _141776 : Type'} (P : type908 _141774 _141775 _141776) (x : type2 _141774 _141775 _141776) : (term18 _141774 _141775 _141776 x P) = (term19 _141774 _141775 _141776 P x).
Proof. exact (@lem8001398 (type2 _141774 _141775 _141776) P x). Qed.
Lemma lem8001400 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term20 _141774 _141775 _141776 a b P) = (term21 _141774 _141775 _141776 P a b).
Proof. exact (@lem8001399 _141774 _141775 _141776 (term22 _141774 _141775 _141776 P) (@pastecart _141774 _141775 _141776 a b)). Qed.
Lemma lem8001401 {_141774 _141775 _141776 : Type'} (GEN_PVAR_360 : type2 _141774 _141775 _141776) (P : type22 _141774 _141775 _141776) : (term23 _141774 _141775 _141776 P GEN_PVAR_360) = (term24 _141774 _141775 _141776 GEN_PVAR_360 P).
Proof. exact (eq_refl (term23 _141774 _141775 _141776 P GEN_PVAR_360)). Qed.
Lemma lem8001402 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : (term25 _141774 _141775 _141776 P) = (term26 _141774 _141775 _141776 P).
Proof. exact (fun_ext (fun GEN_PVAR_360 : type2 _141774 _141775 _141776 => @lem8001401 _141774 _141775 _141776 GEN_PVAR_360 P)). Qed.
Lemma lem8001403 {_141774 _141775 _141776 : Type'} : (@GSPEC (cart _141774 (finite_sum _141775 _141776))) = (@GSPEC (cart _141774 (finite_sum _141775 _141776))).
Proof. exact (eq_refl (@GSPEC (cart _141774 (finite_sum _141775 _141776)))). Qed.
Lemma lem8001404 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : (term27 _141774 _141775 _141776 P) = (term28 _141774 _141775 _141776 P).
Proof. exact (MK_COMB (@lem8001403 _141774 _141775 _141776) (@lem8001402 _141774 _141775 _141776 P)). Qed.
Lemma lem8001405 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) : (term29 _141774 _141775 _141776 a b) = (term29 _141774 _141775 _141776 a b).
Proof. exact (eq_refl (term29 _141774 _141775 _141776 a b)). Qed.
Lemma lem8001406 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) : (term20 _141774 _141775 _141776 a b P) = (term30 _141774 _141775 _141776 a b P).
Proof. exact (MK_COMB (@lem8001405 _141774 _141775 _141776 a b) (@lem8001404 _141774 _141775 _141776 P)). Qed.
Lemma lem8001407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8001408 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) : (term31 _141774 _141775 _141776 a b P) = (term32 _141774 _141775 _141776 a b P).
Proof. exact (MK_COMB (@lem8001407) (@lem8001406 _141774 _141775 _141776 a b P)). Qed.
Lemma lem8001409 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) : (term21 _141774 _141775 _141776 P a b) = (term33 _141774 _141775 _141776 a b P).
Proof. exact (eq_refl (term21 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001410 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) : ((term20 _141774 _141775 _141776 a b P) = (term21 _141774 _141775 _141776 P a b)) = ((term30 _141774 _141775 _141776 a b P) = (term33 _141774 _141775 _141776 a b P)).
Proof. exact (MK_COMB (@lem8001408 _141774 _141775 _141776 a b P) (@lem8001409 _141774 _141775 _141776 a b P)). Qed.
Lemma lem8001411 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) : (term30 _141774 _141775 _141776 a b P) = (term33 _141774 _141775 _141776 a b P).
Proof. exact (EQ_MP (@lem8001410 _141774 _141775 _141776 a b P) (@lem8001400 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001421 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8001422 {_141774 _141775 _141776 : Type'} (f : type1526 _141774 _141775 _141776) (y : Prop) : (term35 _141774 _141775 _141776 f y) = (f y).
Proof. exact (@lem8001421 Prop (type16 _141774 _141775 _141776) f y). Qed.
Lemma lem8001423 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term36 _141774 _141775 _141776 a b P x y) = (term37 _141774 _141775 _141776 a b P x y).
Proof. exact (@lem8001422 _141774 _141775 _141776 (term38 _141774 _141775 _141776 a b) (P x y)). Qed.
Lemma lem8001424 {_141774 _141775 _141776 : Type'} (p : Prop) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term39 _141774 _141775 _141776 a b p) = (term40 _141774 _141775 _141776 p a b).
Proof. exact (eq_refl (term39 _141774 _141775 _141776 a b p)). Qed.
Lemma lem8001425 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) : (term41 _141774 _141775 _141776 a b) = (term38 _141774 _141775 _141776 a b).
Proof. exact (fun_ext (fun p : Prop => @lem8001424 _141774 _141775 _141776 p a b)). Qed.
Lemma lem8001426 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem8001427 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term36 _141774 _141775 _141776 a b P x y) = (term37 _141774 _141775 _141776 a b P x y).
Proof. exact (MK_COMB (@lem8001425 _141774 _141775 _141776 a b) (@lem8001426 _141774 _141775 _141776 P x y)). Qed.
Lemma lem8001428 {_141774 _141775 _141776 : Type'} : (@eq ((cart _141774 (finite_sum _141775 _141776)) -> Prop)) = (@eq ((cart _141774 (finite_sum _141775 _141776)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _141774 (finite_sum _141775 _141776)) -> Prop))). Qed.
Lemma lem8001429 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term42 _141774 _141775 _141776 a b P x y) = (term43 _141774 _141775 _141776 a b P x y).
Proof. exact (MK_COMB (@lem8001428 _141774 _141775 _141776) (@lem8001427 _141774 _141775 _141776 a b P x y)). Qed.
Lemma lem8001430 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term37 _141774 _141775 _141776 a b P x y) = (term44 _141774 _141775 _141776 P x y a b).
Proof. exact (eq_refl (term37 _141774 _141775 _141776 a b P x y)). Qed.
Lemma lem8001431 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term36 _141774 _141775 _141776 a b P x y) = (term37 _141774 _141775 _141776 a b P x y)) = ((term37 _141774 _141775 _141776 a b P x y) = (term44 _141774 _141775 _141776 P x y a b)).
Proof. exact (MK_COMB (@lem8001429 _141774 _141775 _141776 a b P x y) (@lem8001430 _141774 _141775 _141776 P x y a b)). Qed.
Lemma lem8001432 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term37 _141774 _141775 _141776 a b P x y) = (term44 _141774 _141775 _141776 P x y a b).
Proof. exact (EQ_MP (@lem8001431 _141774 _141775 _141776 P x y a b) (@lem8001423 _141774 _141775 _141776 a b P x y)). Qed.
Lemma lem8001438 {_140423 _140433 _140434 : Type'} (x : type3 _140423 _140433 _140434) (y : type3 _140423 _140433 _140434) : (x = y) = (term11 _140423 _140433 _140434 x y).
Proof. exact (EQ_MP (@lem8001341 _140423 _140433 _140434 x y) (@lem8001340 _140423 _140433 _140434 x y)). Qed.
Lemma lem8001439 {_141774 _141775 _141776 : Type'} (x : type2 _141774 _141775 _141776) (y : type2 _141774 _141775 _141776) : (x = y) = (term45 _141774 _141775 _141776 x y).
Proof. exact (@lem8001438 _141775 _141774 _141776 x y). Qed.
Lemma lem8001440 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (t : type2 _141774 _141775 _141776) : ((@pastecart _141774 _141775 _141776 a b) = t) = (term46 _141774 _141775 _141776 a b t).
Proof. exact (@lem8001439 _141774 _141775 _141776 (@pastecart _141774 _141775 _141776 a b) t). Qed.
Lemma lem8001448 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (EQ_MP (@lem8001335 A M N y x) (@lem8001334 A M N x y)). Qed.
Lemma lem8001449 {_141774 _141775 _141776 : Type'} (y : cart _141774 _141776) (x : cart _141774 _141775) : (term7 _141774 _141775 _141776 x y) = x.
Proof. exact (@lem8001448 _141774 _141775 _141776 y x). Qed.
Lemma lem8001450 {_141774 _141775 _141776 : Type'} (b : cart _141774 _141776) (a : cart _141774 _141775) : (term7 _141774 _141775 _141776 a b) = a.
Proof. exact (@lem8001449 _141774 _141775 _141776 b a). Qed.
Lemma lem8001451 {_141774 _141775 : Type'} : (@eq (cart _141774 _141775)) = (@eq (cart _141774 _141775)).
Proof. exact (eq_refl (@eq (cart _141774 _141775))). Qed.
Lemma lem8001452 {_141774 _141775 _141776 : Type'} (b : cart _141774 _141776) (a : cart _141774 _141775) : (term47 _141774 _141775 _141776 a b) = (@eq (cart _141774 _141775) a).
Proof. exact (MK_COMB (@lem8001451 _141774 _141775) (@lem8001450 _141774 _141775 _141776 b a)). Qed.
Lemma lem8001453 {_141774 _141775 _141776 : Type'} (t : type2 _141774 _141775 _141776) : (@fstcart _141774 _141775 _141776 t) = (@fstcart _141774 _141775 _141776 t).
Proof. exact (eq_refl (@fstcart _141774 _141775 _141776 t)). Qed.
Lemma lem8001454 {_141774 _141775 _141776 : Type'} (b : cart _141774 _141776) (a : cart _141774 _141775) (t : type2 _141774 _141775 _141776) : ((term7 _141774 _141775 _141776 a b) = (@fstcart _141774 _141775 _141776 t)) = (a = (@fstcart _141774 _141775 _141776 t)).
Proof. exact (MK_COMB (@lem8001452 _141774 _141775 _141776 b a) (@lem8001453 _141774 _141775 _141776 t)). Qed.
Lemma lem8001459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001460 {_141774 _141775 _141776 : Type'} (b : cart _141774 _141776) (a : cart _141774 _141775) (t : type2 _141774 _141775 _141776) : (term48 _141774 _141775 _141776 a b t) = (term49 _141774 _141775 _141776 a t).
Proof. exact (MK_COMB (@lem8001459) (@lem8001454 _141774 _141775 _141776 b a t)). Qed.
Lemma lem8001466 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem8001329 A M N x y) (@lem8001328 A M N x y)). Qed.
Lemma lem8001467 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) : (term3 _141774 _141775 _141776 x y) = y.
Proof. exact (@lem8001466 _141774 _141775 _141776 x y). Qed.
Lemma lem8001468 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) : (term3 _141774 _141775 _141776 a b) = b.
Proof. exact (@lem8001467 _141774 _141775 _141776 a b). Qed.
Lemma lem8001469 {_141774 _141776 : Type'} : (@eq (cart _141774 _141776)) = (@eq (cart _141774 _141776)).
Proof. exact (eq_refl (@eq (cart _141774 _141776))). Qed.
Lemma lem8001470 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) : (term50 _141774 _141775 _141776 a b) = (@eq (cart _141774 _141776) b).
Proof. exact (MK_COMB (@lem8001469 _141774 _141776) (@lem8001468 _141774 _141775 _141776 a b)). Qed.
Lemma lem8001471 {_141774 _141775 _141776 : Type'} (t : type2 _141774 _141775 _141776) : (@sndcart _141774 _141775 _141776 t) = (@sndcart _141774 _141775 _141776 t).
Proof. exact (eq_refl (@sndcart _141774 _141775 _141776 t)). Qed.
Lemma lem8001472 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (t : type2 _141774 _141775 _141776) : ((term3 _141774 _141775 _141776 a b) = (@sndcart _141774 _141775 _141776 t)) = (b = (@sndcart _141774 _141775 _141776 t)).
Proof. exact (MK_COMB (@lem8001470 _141774 _141775 _141776 a b) (@lem8001471 _141774 _141775 _141776 t)). Qed.
Lemma lem8001477 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (t : type2 _141774 _141775 _141776) : (term46 _141774 _141775 _141776 a b t) = (term51 _141774 _141775 _141776 a b t).
Proof. exact (MK_COMB (@lem8001460 _141774 _141775 _141776 b a t) (@lem8001472 _141774 _141775 _141776 a b t)). Qed.
Lemma lem8001480 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) (t : type2 _141774 _141775 _141776) : ((@pastecart _141774 _141775 _141776 a b) = t) = (term51 _141774 _141775 _141776 a b t).
Proof. exact (TRANS (@lem8001440 _141774 _141775 _141776 a b t) (@lem8001477 _141774 _141775 _141776 a b t)). Qed.
Lemma lem8001481 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term52 _141774 _141775 _141776 P x y) = (term52 _141774 _141775 _141776 P x y).
Proof. exact (eq_refl (term52 _141774 _141775 _141776 P x y)). Qed.
Lemma lem8001482 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (t : type2 _141774 _141775 _141776) : (term53 _141774 _141775 _141776 P x y a b t) = (term54 _141774 _141775 _141776 P x y a b t).
Proof. exact (MK_COMB (@lem8001481 _141774 _141775 _141776 P x y) (@lem8001480 _141774 _141775 _141776 a b t)). Qed.
Lemma lem8001485 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term44 _141774 _141775 _141776 P x y a b) = (term55 _141774 _141775 _141776 P x y a b).
Proof. exact (fun_ext (fun t : type2 _141774 _141775 _141776 => @lem8001482 _141774 _141775 _141776 P x y a b t)). Qed.
Lemma lem8001486 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term37 _141774 _141775 _141776 a b P x y) = (term55 _141774 _141775 _141776 P x y a b).
Proof. exact (TRANS (@lem8001432 _141774 _141775 _141776 P x y a b) (@lem8001485 _141774 _141775 _141776 P x y a b)). Qed.
Lemma lem8001487 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) : (@pastecart _141774 _141775 _141776 x y) = (@pastecart _141774 _141775 _141776 x y).
Proof. exact (eq_refl (@pastecart _141774 _141775 _141776 x y)). Qed.
Lemma lem8001488 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term56 _141774 _141775 _141776 a b P x y) = (term57 _141774 _141775 _141776 P a b x y).
Proof. exact (MK_COMB (@lem8001486 _141774 _141775 _141776 P x y a b) (@lem8001487 _141774 _141775 _141776 x y)). Qed.
Lemma lem8001490 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8001491 {_141774 _141775 _141776 : Type'} (f : type16 _141774 _141775 _141776) (y : type2 _141774 _141775 _141776) : (term58 _141774 _141775 _141776 f y) = (f y).
Proof. exact (@lem8001490 (type2 _141774 _141775 _141776) Prop f y). Qed.
Lemma lem8001492 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term59 _141774 _141775 _141776 P a b x y) = (term57 _141774 _141775 _141776 P a b x y).
Proof. exact (@lem8001491 _141774 _141775 _141776 (term55 _141774 _141775 _141776 P x y a b) (@pastecart _141774 _141775 _141776 x y)). Qed.
Lemma lem8001493 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (t : type2 _141774 _141775 _141776) : (term60 _141774 _141775 _141776 P x y a b t) = (term54 _141774 _141775 _141776 P x y a b t).
Proof. exact (eq_refl (term60 _141774 _141775 _141776 P x y a b t)). Qed.
Lemma lem8001494 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term61 _141774 _141775 _141776 P x y a b) = (term55 _141774 _141775 _141776 P x y a b).
Proof. exact (fun_ext (fun t : type2 _141774 _141775 _141776 => @lem8001493 _141774 _141775 _141776 P x y a b t)). Qed.
Lemma lem8001495 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) : (@pastecart _141774 _141775 _141776 x y) = (@pastecart _141774 _141775 _141776 x y).
Proof. exact (eq_refl (@pastecart _141774 _141775 _141776 x y)). Qed.
Lemma lem8001496 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term59 _141774 _141775 _141776 P a b x y) = (term57 _141774 _141775 _141776 P a b x y).
Proof. exact (MK_COMB (@lem8001494 _141774 _141775 _141776 P x y a b) (@lem8001495 _141774 _141775 _141776 x y)). Qed.
Lemma lem8001497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8001498 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term62 _141774 _141775 _141776 P a b x y) = (term63 _141774 _141775 _141776 P a b x y).
Proof. exact (MK_COMB (@lem8001497) (@lem8001496 _141774 _141775 _141776 P a b x y)). Qed.
Lemma lem8001499 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term57 _141774 _141775 _141776 P a b x y) = (term64 _141774 _141775 _141776 P a b x y).
Proof. exact (eq_refl (term57 _141774 _141775 _141776 P a b x y)). Qed.
Lemma lem8001500 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : ((term59 _141774 _141775 _141776 P a b x y) = (term57 _141774 _141775 _141776 P a b x y)) = ((term57 _141774 _141775 _141776 P a b x y) = (term64 _141774 _141775 _141776 P a b x y)).
Proof. exact (MK_COMB (@lem8001498 _141774 _141775 _141776 P a b x y) (@lem8001499 _141774 _141775 _141776 P a b x y)). Qed.
Lemma lem8001501 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term57 _141774 _141775 _141776 P a b x y) = (term64 _141774 _141775 _141776 P a b x y).
Proof. exact (EQ_MP (@lem8001500 _141774 _141775 _141776 P a b x y) (@lem8001492 _141774 _141775 _141776 P a b x y)). Qed.
Lemma lem8001511 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (EQ_MP (@lem8001335 A M N y x) (@lem8001334 A M N x y)). Qed.
Lemma lem8001512 {_141774 _141775 _141776 : Type'} (y : cart _141774 _141776) (x : cart _141774 _141775) : (term7 _141774 _141775 _141776 x y) = x.
Proof. exact (@lem8001511 _141774 _141775 _141776 y x). Qed.
Lemma lem8001513 {_141774 _141775 : Type'} (a : cart _141774 _141775) : (@eq (cart _141774 _141775) a) = (@eq (cart _141774 _141775) a).
Proof. exact (eq_refl (@eq (cart _141774 _141775) a)). Qed.
Lemma lem8001514 {_141774 _141775 _141776 : Type'} (y : cart _141774 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) : (a = (term7 _141774 _141775 _141776 x y)) = (a = x).
Proof. exact (MK_COMB (@lem8001513 _141774 _141775 a) (@lem8001512 _141774 _141775 _141776 y x)). Qed.
Lemma lem8001519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001520 {_141774 _141775 _141776 : Type'} (y : cart _141774 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) : (term65 _141774 _141775 _141776 a x y) = (term66 _141774 _141775 a x).
Proof. exact (MK_COMB (@lem8001519) (@lem8001514 _141774 _141775 _141776 y a x)). Qed.
Lemma lem8001526 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem8001329 A M N x y) (@lem8001328 A M N x y)). Qed.
Lemma lem8001527 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) : (term3 _141774 _141775 _141776 x y) = y.
Proof. exact (@lem8001526 _141774 _141775 _141776 x y). Qed.
Lemma lem8001528 {_141774 _141776 : Type'} (b : cart _141774 _141776) : (@eq (cart _141774 _141776) b) = (@eq (cart _141774 _141776) b).
Proof. exact (eq_refl (@eq (cart _141774 _141776) b)). Qed.
Lemma lem8001529 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (b = (term3 _141774 _141775 _141776 x y)) = (b = y).
Proof. exact (MK_COMB (@lem8001528 _141774 _141776 b) (@lem8001527 _141774 _141775 _141776 x y)). Qed.
Lemma lem8001534 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term67 _141774 _141775 _141776 a b x y) = (term68 _141774 _141775 _141776 a x b y).
Proof. exact (MK_COMB (@lem8001520 _141774 _141775 _141776 y a x) (@lem8001529 _141774 _141775 _141776 x b y)). Qed.
Lemma lem8001537 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term52 _141774 _141775 _141776 P x y) = (term52 _141774 _141775 _141776 P x y).
Proof. exact (eq_refl (term52 _141774 _141775 _141776 P x y)). Qed.
Lemma lem8001538 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term64 _141774 _141775 _141776 P a b x y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (MK_COMB (@lem8001537 _141774 _141775 _141776 P x y) (@lem8001534 _141774 _141775 _141776 a x b y)). Qed.
Lemma lem8001541 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term57 _141774 _141775 _141776 P a b x y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (TRANS (@lem8001501 _141774 _141775 _141776 P a b x y) (@lem8001538 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001542 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term56 _141774 _141775 _141776 a b P x y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (TRANS (@lem8001488 _141774 _141775 _141776 P a b x y) (@lem8001541 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001543 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term70 _141774 _141775 _141776 a b P x) = (term71 _141774 _141775 _141776 P a x b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8001542 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001544 {_141774 _141776 : Type'} : (@ex (cart _141774 _141776)) = (@ex (cart _141774 _141776)).
Proof. exact (eq_refl (@ex (cart _141774 _141776))). Qed.
Lemma lem8001545 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term72 _141774 _141775 _141776 a b P x) = (term73 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001544 _141774 _141776) (@lem8001543 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001550 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term74 _141774 _141775 _141776 a b P) = (term75 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001545 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001551 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8001552 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term33 _141774 _141775 _141776 a b P) = (term76 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001551 _141774 _141775) (@lem8001550 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001557 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term30 _141774 _141775 _141776 a b P) = (term76 _141774 _141775 _141776 P a b).
Proof. exact (TRANS (@lem8001411 _141774 _141775 _141776 a b P) (@lem8001552 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8001559 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term32 _141774 _141775 _141776 a b P) = (term77 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001558) (@lem8001557 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001560 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem8001561 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term30 _141774 _141775 _141776 a b P) = (P a b)) = ((term76 _141774 _141775 _141776 P a b) = (P a b)).
Proof. exact (MK_COMB (@lem8001559 _141774 _141775 _141776 P a b) (@lem8001560 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001566 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : (term78 _141774 _141775 _141776 P a) = (term79 _141774 _141775 _141776 P a).
Proof. exact (fun_ext (fun b : cart _141774 _141776 => @lem8001561 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001567 {_141774 _141776 : Type'} : (@all (cart _141774 _141776)) = (@all (cart _141774 _141776)).
Proof. exact (eq_refl (@all (cart _141774 _141776))). Qed.
Lemma lem8001568 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : (term80 _141774 _141775 _141776 P a) = (term81 _141774 _141775 _141776 P a).
Proof. exact (MK_COMB (@lem8001567 _141774 _141776) (@lem8001566 _141774 _141775 _141776 P a)). Qed.
Lemma lem8001573 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : (term82 _141774 _141775 _141776 P) = (term83 _141774 _141775 _141776 P).
Proof. exact (fun_ext (fun a : cart _141774 _141775 => @lem8001568 _141774 _141775 _141776 P a)). Qed.
Lemma lem8001574 {_141774 _141775 : Type'} : (@all (cart _141774 _141775)) = (@all (cart _141774 _141775)).
Proof. exact (eq_refl (@all (cart _141774 _141775))). Qed.
Lemma lem8001575 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : (term84 _141774 _141775 _141776 P) = (term85 _141774 _141775 _141776 P).
Proof. exact (MK_COMB (@lem8001574 _141774 _141775) (@lem8001573 _141774 _141775 _141776 P)). Qed.
Lemma lem8001580 {_141774 _141775 _141776 : Type'} : (term86 _141774 _141775 _141776) = (term87 _141774 _141775 _141776).
Proof. exact (fun_ext (fun P : type22 _141774 _141775 _141776 => @lem8001575 _141774 _141775 _141776 P)). Qed.
Lemma lem8001581 {_141774 _141775 _141776 : Type'} : (@all ((cart _141774 _141775) -> (cart _141774 _141776) -> Prop)) = (@all ((cart _141774 _141775) -> (cart _141774 _141776) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141774 _141775) -> (cart _141774 _141776) -> Prop))). Qed.
Lemma lem8001582 {_141774 _141775 _141776 : Type'} : (term88 _141774 _141775 _141776) = (term89 _141774 _141775 _141776).
Proof. exact (MK_COMB (@lem8001581 _141774 _141775 _141776) (@lem8001580 _141774 _141775 _141776)). Qed.
Lemma lem8001587 {_141774 _141775 _141776 : Type'} : (term89 _141774 _141775 _141776) = (term88 _141774 _141775 _141776).
Proof. exact (SYM (@lem8001582 _141774 _141775 _141776)). Qed.
Lemma lem8001589 (p : Prop) : p = (term90 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8001590 {_141774 _141775 _141776 : Type'} : (term89 _141774 _141775 _141776) = (term91 _141774 _141775 _141776).
Proof. exact (@lem8001589 (term89 _141774 _141775 _141776)). Qed.
Lemma lem8001591 {_141774 _141775 _141776 : Type'} : (term91 _141774 _141775 _141776) = (term89 _141774 _141775 _141776).
Proof. exact (SYM (@lem8001590 _141774 _141775 _141776)). Qed.
Lemma lem8001592 {_141774 _141775 _141776 : Type'} (h1 : term92 _141774 _141775 _141776) : term92 _141774 _141775 _141776.
Proof. exact (h1). Qed.
Lemma lem8001595 {_141774 _141775 _141776 : Type'} (h1 : term91 _141774 _141775 _141776) : term91 _141774 _141775 _141776.
Proof. exact (h1). Qed.
Lemma lem8001596 {_141774 _141775 _141776 : Type'} : term93 _141774 _141775 _141776.
Proof. exact (fun h0 : term91 _141774 _141775 _141776 => @lem8001595 _141774 _141775 _141776 h0). Qed.
Lemma lem8001597 {_141774 _141775 _141776 : Type'} (h1 : term93 _141774 _141775 _141776) : term93 _141774 _141775 _141776.
Proof. exact (h1). Qed.
Lemma lem8001598 {_141774 _141775 _141776 : Type'} (h1 : term91 _141774 _141775 _141776) : term91 _141774 _141775 _141776.
Proof. exact (h1). Qed.
Lemma lem8001599 {_141774 _141775 _141776 : Type'} (h1 : term91 _141774 _141775 _141776) (h2 : term93 _141774 _141775 _141776) : term91 _141774 _141775 _141776.
Proof. exact (@lem8001597 _141774 _141775 _141776 h2 (@lem8001598 _141774 _141775 _141776 h1)). Qed.
Lemma lem8001600 {_141774 _141775 _141776 : Type'} (h1 : term91 _141774 _141775 _141776) : term94 _141774 _141775 _141776.
Proof. exact (fun h0 : term93 _141774 _141775 _141776 => @lem8001599 _141774 _141775 _141776 h1 h0). Qed.
Lemma lem8001601 {_141774 _141775 _141776 : Type'} (h1 : term93 _141774 _141775 _141776) : term93 _141774 _141775 _141776.
Proof. exact (h1). Qed.
Lemma lem8001602 {_141774 _141775 _141776 : Type'} (h1 : term91 _141774 _141775 _141776) (h2 : term93 _141774 _141775 _141776) : term91 _141774 _141775 _141776.
Proof. exact (@lem8001600 _141774 _141775 _141776 h1 (@lem8001601 _141774 _141775 _141776 h2)). Qed.
Lemma lem8001603 {_141774 _141775 _141776 : Type'} (h1 : term93 _141774 _141775 _141776) : term93 _141774 _141775 _141776.
Proof. exact (fun h0 : term91 _141774 _141775 _141776 => @lem8001602 _141774 _141775 _141776 h0 h1). Qed.
Lemma lem8001604 {_141774 _141775 _141776 : Type'} : term95 _141774 _141775 _141776.
Proof. exact (fun h0 : term93 _141774 _141775 _141776 => @lem8001603 _141774 _141775 _141776 h0). Qed.
Lemma lem8001607 {_141774 _141775 _141776 : Type'} : term93 _141774 _141775 _141776.
Proof. exact (@lem8001604 _141774 _141775 _141776 (@lem8001596 _141774 _141775 _141776)). Qed.
Lemma lem8001608 {_141774 _141775 _141776 : Type'} : term93 _141774 _141775 _141776.
Proof. exact (@lem8001607 _141774 _141775 _141776). Qed.
Lemma lem8001610 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8001611 {_141774 _141775 _141776 : Type'} : (term91 _141774 _141775 _141776) = (term96 _141774 _141775 _141776).
Proof. exact (@lem8001610 (term92 _141774 _141775 _141776)). Qed.
Lemma lem8001613 (t : Prop) : (term97 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8001614 {_141774 _141775 _141776 : Type'} : (term96 _141774 _141775 _141776) = (term89 _141774 _141775 _141776).
Proof. exact (@lem8001613 (term89 _141774 _141775 _141776)). Qed.
Lemma lem8001687 {_141774 _141775 _141776 : Type'} : (term91 _141774 _141775 _141776) = (term89 _141774 _141775 _141776).
Proof. exact (TRANS (@lem8001611 _141774 _141775 _141776) (@lem8001614 _141774 _141775 _141776)). Qed.
Lemma lem8001688 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem8001697 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term69 _141774 _141775 _141776 P a x b y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (eq_refl (term69 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001698 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term71 _141774 _141775 _141776 P a x b) = (term71 _141774 _141775 _141776 P a x b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8001697 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001699 {_141774 _141776 : Type'} : (@ex (cart _141774 _141776)) = (@ex (cart _141774 _141776)).
Proof. exact (eq_refl (@ex (cart _141774 _141776))). Qed.
Lemma lem8001700 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term73 _141774 _141775 _141776 P a x b) = (term73 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001699 _141774 _141776) (@lem8001698 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001701 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term75 _141774 _141775 _141776 P a b) = (term75 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001700 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001702 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8001703 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term76 _141774 _141775 _141776 P a b) = (term76 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001702 _141774 _141775) (@lem8001701 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8001705 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term77 _141774 _141775 _141776 P a b) = (term77 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001704) (@lem8001703 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001706 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term76 _141774 _141775 _141776 P a b) = (P a b)) = ((term76 _141774 _141775 _141776 P a b) = (P a b)).
Proof. exact (MK_COMB (@lem8001705 _141774 _141775 _141776 P a b) (@lem8001688 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001707 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : (term79 _141774 _141775 _141776 P a) = (term79 _141774 _141775 _141776 P a).
Proof. exact (fun_ext (fun b : cart _141774 _141776 => @lem8001706 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001708 {_141774 _141776 : Type'} : (@all (cart _141774 _141776)) = (@all (cart _141774 _141776)).
Proof. exact (eq_refl (@all (cart _141774 _141776))). Qed.
Lemma lem8001709 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : (term81 _141774 _141775 _141776 P a) = (term81 _141774 _141775 _141776 P a).
Proof. exact (MK_COMB (@lem8001708 _141774 _141776) (@lem8001707 _141774 _141775 _141776 P a)). Qed.
Lemma lem8001710 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : (term83 _141774 _141775 _141776 P) = (term83 _141774 _141775 _141776 P).
Proof. exact (fun_ext (fun a : cart _141774 _141775 => @lem8001709 _141774 _141775 _141776 P a)). Qed.
Lemma lem8001711 {_141774 _141775 : Type'} : (@all (cart _141774 _141775)) = (@all (cart _141774 _141775)).
Proof. exact (eq_refl (@all (cart _141774 _141775))). Qed.
Lemma lem8001712 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : (term85 _141774 _141775 _141776 P) = (term85 _141774 _141775 _141776 P).
Proof. exact (MK_COMB (@lem8001711 _141774 _141775) (@lem8001710 _141774 _141775 _141776 P)). Qed.
Lemma lem8001713 {_141774 _141775 _141776 : Type'} : (term87 _141774 _141775 _141776) = (term87 _141774 _141775 _141776).
Proof. exact (fun_ext (fun P : type22 _141774 _141775 _141776 => @lem8001712 _141774 _141775 _141776 P)). Qed.
Lemma lem8001714 {_141774 _141775 _141776 : Type'} : (@all ((cart _141774 _141775) -> (cart _141774 _141776) -> Prop)) = (@all ((cart _141774 _141775) -> (cart _141774 _141776) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141774 _141775) -> (cart _141774 _141776) -> Prop))). Qed.
Lemma lem8001715 {_141774 _141775 _141776 : Type'} : (term89 _141774 _141775 _141776) = (term89 _141774 _141775 _141776).
Proof. exact (MK_COMB (@lem8001714 _141774 _141775 _141776) (@lem8001713 _141774 _141775 _141776)). Qed.
Lemma lem8001752 {_141774 _141775 _141776 : Type'} : (term91 _141774 _141775 _141776) = (term89 _141774 _141775 _141776).
Proof. exact (TRANS (@lem8001687 _141774 _141775 _141776) (@lem8001715 _141774 _141775 _141776)). Qed.
Lemma lem8001753 {_141774 _141775 _141776 : Type'} : (term89 _141774 _141775 _141776) = (term91 _141774 _141775 _141776).
Proof. exact (SYM (@lem8001752 _141774 _141775 _141776)). Qed.
Lemma lem8001755 (p : Prop) : p = (term90 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8001756 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term76 _141774 _141775 _141776 P a b) = (P a b)) = (term98 _141774 _141775 _141776 P a b).
Proof. exact (@lem8001755 ((term76 _141774 _141775 _141776 P a b) = (P a b))). Qed.
Lemma lem8001757 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term98 _141774 _141775 _141776 P a b) = ((term76 _141774 _141775 _141776 P a b) = (P a b)).
Proof. exact (SYM (@lem8001756 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001758 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term99 _141774 _141775 _141776 P a b) : term99 _141774 _141775 _141776 P a b.
Proof. exact (h1). Qed.
Lemma lem8001769 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term100 _141774 _141775 _141776 a x b y) = (term101 _141774 _141775 _141776 a x b y).
Proof. exact (@lem17045 (a = x) (b = y)). Qed.
Lemma lem8001774 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term102 _141774 _141775 _141776 P x y) = (term102 _141774 _141775 _141776 P x y).
Proof. exact (eq_refl (term102 _141774 _141775 _141776 P x y)). Qed.
Lemma lem8001775 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term103 _141774 _141775 _141776 P a x b y) = (term104 _141774 _141775 _141776 P a x b y).
Proof. exact (MK_COMB (@lem8001774 _141774 _141775 _141776 P x y) (@lem8001769 _141774 _141775 _141776 a x b y)). Qed.
Lemma lem8001776 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term105 _141774 _141775 _141776 P a x b y) = (term103 _141774 _141775 _141776 P a x b y).
Proof. exact (@lem17045 (P x y) (term68 _141774 _141775 _141776 a x b y)). Qed.
Lemma lem8001777 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term105 _141774 _141775 _141776 P a x b y) = (term104 _141774 _141775 _141776 P a x b y).
Proof. exact (TRANS (@lem8001776 _141774 _141775 _141776 P a x b y) (@lem8001775 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001780 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term69 _141774 _141775 _141776 P a x b y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (eq_refl (term69 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001781 {_141774 _141776 : Type'} (P : type24 _141774 _141776) : (term106 _141774 _141776 P) = (term107 _141774 _141776 P).
Proof. exact (@lem18394 (cart _141774 _141776) P). Qed.
Lemma lem8001782 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term108 _141774 _141775 _141776 P a x b) = (term109 _141774 _141775 _141776 P a x b).
Proof. exact (@lem8001781 _141774 _141776 (term71 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001783 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term110 _141774 _141775 _141776 P a x b y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (eq_refl (term110 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001784 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8001785 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term111 _141774 _141775 _141776 P a x b y) = (term105 _141774 _141775 _141776 P a x b y).
Proof. exact (MK_COMB (@lem8001784) (@lem8001783 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001786 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term111 _141774 _141775 _141776 P a x b y) = (term104 _141774 _141775 _141776 P a x b y).
Proof. exact (TRANS (@lem8001785 _141774 _141775 _141776 P a x b y) (@lem8001777 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001787 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term112 _141774 _141775 _141776 P a x b) = (term113 _141774 _141775 _141776 P a x b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8001786 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001788 {_141774 _141776 : Type'} : (@all (cart _141774 _141776)) = (@all (cart _141774 _141776)).
Proof. exact (eq_refl (@all (cart _141774 _141776))). Qed.
Lemma lem8001789 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term109 _141774 _141775 _141776 P a x b) = (term114 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001788 _141774 _141776) (@lem8001787 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001790 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term108 _141774 _141775 _141776 P a x b) = (term114 _141774 _141775 _141776 P a x b).
Proof. exact (TRANS (@lem8001782 _141774 _141775 _141776 P a x b) (@lem8001789 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001791 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term71 _141774 _141775 _141776 P a x b) = (term71 _141774 _141775 _141776 P a x b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8001780 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001792 {_141774 _141776 : Type'} : (@ex (cart _141774 _141776)) = (@ex (cart _141774 _141776)).
Proof. exact (eq_refl (@ex (cart _141774 _141776))). Qed.
Lemma lem8001793 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term73 _141774 _141775 _141776 P a x b) = (term73 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001792 _141774 _141776) (@lem8001791 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001794 {_141774 _141775 : Type'} (P : type24 _141774 _141775) : (term106 _141774 _141775 P) = (term107 _141774 _141775 P).
Proof. exact (@lem18394 (cart _141774 _141775) P). Qed.
Lemma lem8001795 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term115 _141774 _141775 _141776 P a b) = (term116 _141774 _141775 _141776 P a b).
Proof. exact (@lem8001794 _141774 _141775 (term75 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001796 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term117 _141774 _141775 _141776 P a b x) = (term73 _141774 _141775 _141776 P a x b).
Proof. exact (eq_refl (term117 _141774 _141775 _141776 P a b x)). Qed.
Lemma lem8001797 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8001798 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term118 _141774 _141775 _141776 P a b x) = (term108 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001797) (@lem8001796 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001799 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term118 _141774 _141775 _141776 P a b x) = (term114 _141774 _141775 _141776 P a x b).
Proof. exact (TRANS (@lem8001798 _141774 _141775 _141776 P a x b) (@lem8001790 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001800 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term119 _141774 _141775 _141776 P a b) = (term120 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001799 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001801 {_141774 _141775 : Type'} : (@all (cart _141774 _141775)) = (@all (cart _141774 _141775)).
Proof. exact (eq_refl (@all (cart _141774 _141775))). Qed.
Lemma lem8001802 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term116 _141774 _141775 _141776 P a b) = (term121 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001801 _141774 _141775) (@lem8001800 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001803 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term115 _141774 _141775 _141776 P a b) = (term121 _141774 _141775 _141776 P a b).
Proof. exact (TRANS (@lem8001795 _141774 _141775 _141776 P a b) (@lem8001802 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001804 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term75 _141774 _141775 _141776 P a b) = (term75 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001793 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001805 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8001806 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term76 _141774 _141775 _141776 P a b) = (term76 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001805 _141774 _141775) (@lem8001804 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001807 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term122 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001808 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem8001809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001810 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term123 _141774 _141775 _141776 P a b) = (term124 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001809) (@lem8001803 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001811 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term125 _141774 _141775 _141776 P a b) = (term126 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001810 _141774 _141775 _141776 P a b) (@lem8001808 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001813 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term127 _141774 _141775 _141776 P a b) = (term127 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001812) (@lem8001806 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001814 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term128 _141774 _141775 _141776 P a b) = (term128 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001813 _141774 _141775 _141776 P a b) (@lem8001807 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8001816 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term129 _141774 _141775 _141776 P a b) = (term129 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001815) (@lem8001814 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001817 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term130 _141774 _141775 _141776 P a b) = (term131 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001816 _141774 _141775 _141776 P a b) (@lem8001811 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001818 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term99 _141774 _141775 _141776 P a b) = (term130 _141774 _141775 _141776 P a b).
Proof. exact (@lem17646 (term76 _141774 _141775 _141776 P a b) (P a b)). Qed.
Lemma lem8001819 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term99 _141774 _141775 _141776 P a b) = (term131 _141774 _141775 _141776 P a b).
Proof. exact (TRANS (@lem8001818 _141774 _141775 _141776 P a b) (@lem8001817 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001926 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8001927 {_141774 _141775 : Type'} (P : type24 _141774 _141775) (Q : Prop) : (term134 _141774 _141775 P Q) = (term135 _141774 _141775 P Q).
Proof. exact (@lem8001926 (cart _141774 _141775) P Q). Qed.
Lemma lem8001928 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term136 _141774 _141775 _141776 P a b) = (term137 _141774 _141775 _141776 P a b).
Proof. exact (@lem8001927 _141774 _141775 (term75 _141774 _141775 _141776 P a b) (term122 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001929 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term117 _141774 _141775 _141776 P a b x) = (term73 _141774 _141775 _141776 P a x b).
Proof. exact (eq_refl (term117 _141774 _141775 _141776 P a b x)). Qed.
Lemma lem8001930 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term138 _141774 _141775 _141776 P a b) = (term75 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001929 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001931 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8001932 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term139 _141774 _141775 _141776 P a b) = (term76 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001931 _141774 _141775) (@lem8001930 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001934 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term140 _141774 _141775 _141776 P a b) = (term127 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001933) (@lem8001932 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001935 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term122 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001936 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term136 _141774 _141775 _141776 P a b) = (term128 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001934 _141774 _141775 _141776 P a b) (@lem8001935 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8001938 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term141 _141774 _141775 _141776 P a b) = (term142 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001937) (@lem8001936 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001939 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term117 _141774 _141775 _141776 P a b x) = (term73 _141774 _141775 _141776 P a x b).
Proof. exact (eq_refl (term117 _141774 _141775 _141776 P a b x)). Qed.
Lemma lem8001940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001941 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term143 _141774 _141775 _141776 P a b x) = (term144 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001940) (@lem8001939 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001942 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term122 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001943 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term145 _141774 _141775 _141776 x P a b) = (term146 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8001941 _141774 _141775 _141776 P a x b) (@lem8001942 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001944 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term147 _141774 _141775 _141776 P a b) = (term148 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001943 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001945 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8001946 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term137 _141774 _141775 _141776 P a b) = (term149 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001945 _141774 _141775) (@lem8001944 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001947 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term136 _141774 _141775 _141776 P a b) = (term137 _141774 _141775 _141776 P a b)) = ((term128 _141774 _141775 _141776 P a b) = (term149 _141774 _141775 _141776 P a b)).
Proof. exact (MK_COMB (@lem8001938 _141774 _141775 _141776 P a b) (@lem8001946 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001948 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term128 _141774 _141775 _141776 P a b) = (term149 _141774 _141775 _141776 P a b).
Proof. exact (EQ_MP (@lem8001947 _141774 _141775 _141776 P a b) (@lem8001928 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001950 {A : Type'} (P : A -> Prop) (Q : Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8001951 {_141774 _141776 : Type'} (P : type24 _141774 _141776) (Q : Prop) : (term134 _141774 _141776 P Q) = (term135 _141774 _141776 P Q).
Proof. exact (@lem8001950 (cart _141774 _141776) P Q). Qed.
Lemma lem8001952 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term150 _141774 _141775 _141776 x P a b) = (term151 _141774 _141775 _141776 x P a b).
Proof. exact (@lem8001951 _141774 _141776 (term71 _141774 _141775 _141776 P a x b) (term122 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001953 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term110 _141774 _141775 _141776 P a x b y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (eq_refl (term110 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001954 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term152 _141774 _141775 _141776 P a x b) = (term71 _141774 _141775 _141776 P a x b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8001953 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001955 {_141774 _141776 : Type'} : (@ex (cart _141774 _141776)) = (@ex (cart _141774 _141776)).
Proof. exact (eq_refl (@ex (cart _141774 _141776))). Qed.
Lemma lem8001956 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term153 _141774 _141775 _141776 P a x b) = (term73 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001955 _141774 _141776) (@lem8001954 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001958 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term154 _141774 _141775 _141776 P a x b) = (term144 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8001957) (@lem8001956 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8001959 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term122 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001960 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term150 _141774 _141775 _141776 x P a b) = (term146 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8001958 _141774 _141775 _141776 P a x b) (@lem8001959 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8001962 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term155 _141774 _141775 _141776 x P a b) = (term156 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8001961) (@lem8001960 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001963 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term110 _141774 _141775 _141776 P a x b y) = (term69 _141774 _141775 _141776 P a x b y).
Proof. exact (eq_refl (term110 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8001965 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term157 _141774 _141775 _141776 P a x b y) = (term158 _141774 _141775 _141776 P a x b y).
Proof. exact (MK_COMB (@lem8001964) (@lem8001963 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8001966 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term122 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001967 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term159 _141774 _141775 _141776 x y P a b) = (term160 _141774 _141775 _141776 x y P a b).
Proof. exact (MK_COMB (@lem8001965 _141774 _141775 _141776 P a x b y) (@lem8001966 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001968 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term161 _141774 _141775 _141776 x P a b) = (term162 _141774 _141775 _141776 x P a b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8001967 _141774 _141775 _141776 x y P a b)). Qed.
Lemma lem8001969 {_141774 _141776 : Type'} : (@ex (cart _141774 _141776)) = (@ex (cart _141774 _141776)).
Proof. exact (eq_refl (@ex (cart _141774 _141776))). Qed.
Lemma lem8001970 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term151 _141774 _141775 _141776 x P a b) = (term163 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8001969 _141774 _141776) (@lem8001968 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001971 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term150 _141774 _141775 _141776 x P a b) = (term151 _141774 _141775 _141776 x P a b)) = ((term146 _141774 _141775 _141776 x P a b) = (term163 _141774 _141775 _141776 x P a b)).
Proof. exact (MK_COMB (@lem8001962 _141774 _141775 _141776 x P a b) (@lem8001970 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001972 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term146 _141774 _141775 _141776 x P a b) = (term163 _141774 _141775 _141776 x P a b).
Proof. exact (EQ_MP (@lem8001971 _141774 _141775 _141776 x P a b) (@lem8001952 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001973 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term148 _141774 _141775 _141776 P a b) = (term164 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001972 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001974 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8001975 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term149 _141774 _141775 _141776 P a b) = (term165 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001974 _141774 _141775) (@lem8001973 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001976 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term128 _141774 _141775 _141776 P a b) = (term165 _141774 _141775 _141776 P a b).
Proof. exact (TRANS (@lem8001948 _141774 _141775 _141776 P a b) (@lem8001975 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8001978 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term129 _141774 _141775 _141776 P a b) = (term166 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001977) (@lem8001976 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001979 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term126 _141774 _141775 _141776 P a b) = (term126 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term126 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001980 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term131 _141774 _141775 _141776 P a b) = (term167 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001978 _141774 _141775 _141776 P a b) (@lem8001979 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001982 {A : Type'} (P : A -> Prop) (Q : Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8001983 {_141774 _141775 : Type'} (P : type24 _141774 _141775) (Q : Prop) : (term170 _141774 _141775 P Q) = (term171 _141774 _141775 P Q).
Proof. exact (@lem8001982 (cart _141774 _141775) P Q). Qed.
Lemma lem8001984 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term172 _141774 _141775 _141776 P a b) = (term173 _141774 _141775 _141776 P a b).
Proof. exact (@lem8001983 _141774 _141775 (term164 _141774 _141775 _141776 P a b) (term126 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001985 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term174 _141774 _141775 _141776 P a b x) = (term163 _141774 _141775 _141776 x P a b).
Proof. exact (eq_refl (term174 _141774 _141775 _141776 P a b x)). Qed.
Lemma lem8001986 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term175 _141774 _141775 _141776 P a b) = (term164 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001985 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001987 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8001988 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term176 _141774 _141775 _141776 P a b) = (term165 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001987 _141774 _141775) (@lem8001986 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8001990 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term177 _141774 _141775 _141776 P a b) = (term166 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001989) (@lem8001988 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001991 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term126 _141774 _141775 _141776 P a b) = (term126 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term126 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001992 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term172 _141774 _141775 _141776 P a b) = (term167 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001990 _141774 _141775 _141776 P a b) (@lem8001991 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8001994 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term178 _141774 _141775 _141776 P a b) = (term179 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8001993) (@lem8001992 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001995 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term174 _141774 _141775 _141776 P a b x) = (term163 _141774 _141775 _141776 x P a b).
Proof. exact (eq_refl (term174 _141774 _141775 _141776 P a b x)). Qed.
Lemma lem8001996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8001997 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term180 _141774 _141775 _141776 P a b x) = (term181 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8001996) (@lem8001995 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8001998 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term126 _141774 _141775 _141776 P a b) = (term126 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term126 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8001999 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term182 _141774 _141775 _141776 x P a b) = (term183 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8001997 _141774 _141775 _141776 x P a b) (@lem8001998 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002000 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term184 _141774 _141775 _141776 P a b) = (term185 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8001999 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002001 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8002002 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term173 _141774 _141775 _141776 P a b) = (term186 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8002001 _141774 _141775) (@lem8002000 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002003 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term172 _141774 _141775 _141776 P a b) = (term173 _141774 _141775 _141776 P a b)) = ((term167 _141774 _141775 _141776 P a b) = (term186 _141774 _141775 _141776 P a b)).
Proof. exact (MK_COMB (@lem8001994 _141774 _141775 _141776 P a b) (@lem8002002 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002004 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term167 _141774 _141775 _141776 P a b) = (term186 _141774 _141775 _141776 P a b).
Proof. exact (EQ_MP (@lem8002003 _141774 _141775 _141776 P a b) (@lem8001984 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002006 {A : Type'} (P : A -> Prop) (Q : Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8002007 {_141774 _141776 : Type'} (P : type24 _141774 _141776) (Q : Prop) : (term170 _141774 _141776 P Q) = (term171 _141774 _141776 P Q).
Proof. exact (@lem8002006 (cart _141774 _141776) P Q). Qed.
Lemma lem8002008 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term187 _141774 _141775 _141776 x P a b) = (term188 _141774 _141775 _141776 x P a b).
Proof. exact (@lem8002007 _141774 _141776 (term162 _141774 _141775 _141776 x P a b) (term126 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002009 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term189 _141774 _141775 _141776 x P a b y) = (term160 _141774 _141775 _141776 x y P a b).
Proof. exact (eq_refl (term189 _141774 _141775 _141776 x P a b y)). Qed.
Lemma lem8002010 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term190 _141774 _141775 _141776 x P a b) = (term162 _141774 _141775 _141776 x P a b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8002009 _141774 _141775 _141776 x y P a b)). Qed.
Lemma lem8002011 {_141774 _141776 : Type'} : (@ex (cart _141774 _141776)) = (@ex (cart _141774 _141776)).
Proof. exact (eq_refl (@ex (cart _141774 _141776))). Qed.
Lemma lem8002012 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term191 _141774 _141775 _141776 x P a b) = (term163 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8002011 _141774 _141776) (@lem8002010 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8002014 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term192 _141774 _141775 _141776 x P a b) = (term181 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8002013) (@lem8002012 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002015 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term126 _141774 _141775 _141776 P a b) = (term126 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term126 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002016 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term187 _141774 _141775 _141776 x P a b) = (term183 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8002014 _141774 _141775 _141776 x P a b) (@lem8002015 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8002018 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term193 _141774 _141775 _141776 x P a b) = (term194 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8002017) (@lem8002016 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002019 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term189 _141774 _141775 _141776 x P a b y) = (term160 _141774 _141775 _141776 x y P a b).
Proof. exact (eq_refl (term189 _141774 _141775 _141776 x P a b y)). Qed.
Lemma lem8002020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8002021 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term195 _141774 _141775 _141776 x P a b y) = (term196 _141774 _141775 _141776 x y P a b).
Proof. exact (MK_COMB (@lem8002020) (@lem8002019 _141774 _141775 _141776 x y P a b)). Qed.
Lemma lem8002022 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term126 _141774 _141775 _141776 P a b) = (term126 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term126 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002023 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term197 _141774 _141775 _141776 x y P a b) = (term198 _141774 _141775 _141776 x y P a b).
Proof. exact (MK_COMB (@lem8002021 _141774 _141775 _141776 x y P a b) (@lem8002022 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002024 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term199 _141774 _141775 _141776 x P a b) = (term200 _141774 _141775 _141776 x P a b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8002023 _141774 _141775 _141776 x y P a b)). Qed.
Lemma lem8002025 {_141774 _141776 : Type'} : (@ex (cart _141774 _141776)) = (@ex (cart _141774 _141776)).
Proof. exact (eq_refl (@ex (cart _141774 _141776))). Qed.
Lemma lem8002026 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term188 _141774 _141775 _141776 x P a b) = (term201 _141774 _141775 _141776 x P a b).
Proof. exact (MK_COMB (@lem8002025 _141774 _141776) (@lem8002024 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002027 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : ((term187 _141774 _141775 _141776 x P a b) = (term188 _141774 _141775 _141776 x P a b)) = ((term183 _141774 _141775 _141776 x P a b) = (term201 _141774 _141775 _141776 x P a b)).
Proof. exact (MK_COMB (@lem8002018 _141774 _141775 _141776 x P a b) (@lem8002026 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002028 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term183 _141774 _141775 _141776 x P a b) = (term201 _141774 _141775 _141776 x P a b).
Proof. exact (EQ_MP (@lem8002027 _141774 _141775 _141776 x P a b) (@lem8002008 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002029 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term185 _141774 _141775 _141776 P a b) = (term202 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8002028 _141774 _141775 _141776 x P a b)). Qed.
Lemma lem8002030 {_141774 _141775 : Type'} : (@ex (cart _141774 _141775)) = (@ex (cart _141774 _141775)).
Proof. exact (eq_refl (@ex (cart _141774 _141775))). Qed.
Lemma lem8002031 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term186 _141774 _141775 _141776 P a b) = (term203 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8002030 _141774 _141775) (@lem8002029 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002032 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term167 _141774 _141775 _141776 P a b) = (term203 _141774 _141775 _141776 P a b).
Proof. exact (TRANS (@lem8002004 _141774 _141775 _141776 P a b) (@lem8002031 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002034 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term131 _141774 _141775 _141776 P a b) = (term203 _141774 _141775 _141776 P a b).
Proof. exact (TRANS (@lem8001980 _141774 _141775 _141776 P a b) (@lem8002032 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002035 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term99 _141774 _141775 _141776 P a b) = (term203 _141774 _141775 _141776 P a b).
Proof. exact (TRANS (@lem8001819 _141774 _141775 _141776 P a b) (@lem8002034 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002036 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term99 _141774 _141775 _141776 P a b) : term203 _141774 _141775 _141776 P a b.
Proof. exact (EQ_MP (@lem8002035 _141774 _141775 _141776 P a b) (@lem8001758 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002037 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term201 _141774 _141775 _141776 x P a b) : term201 _141774 _141775 _141776 x P a b.
Proof. exact (h1). Qed.
Lemma lem8002038 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term198 _141774 _141775 _141776 x y P a b) : term198 _141774 _141775 _141776 x y P a b.
Proof. exact (h1). Qed.
Lemma lem8002043 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (P a b) = (P a b).
Proof. exact (eq_refl (P a b)). Qed.
Lemma lem8002070 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term104 _141774 _141775 _141776 P a x b y) = (term104 _141774 _141775 _141776 P a x b y).
Proof. exact (eq_refl (term104 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8002071 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term113 _141774 _141775 _141776 P a x b) = (term113 _141774 _141775 _141776 P a x b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8002070 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8002072 {_141774 _141776 : Type'} : (@all (cart _141774 _141776)) = (@all (cart _141774 _141776)).
Proof. exact (eq_refl (@all (cart _141774 _141776))). Qed.
Lemma lem8002073 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term114 _141774 _141775 _141776 P a x b) = (term114 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8002072 _141774 _141776) (@lem8002071 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8002074 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term120 _141774 _141775 _141776 P a b) = (term120 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8002073 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8002075 {_141774 _141775 : Type'} : (@all (cart _141774 _141775)) = (@all (cart _141774 _141775)).
Proof. exact (eq_refl (@all (cart _141774 _141775))). Qed.
Lemma lem8002076 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term121 _141774 _141775 _141776 P a b) = (term121 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8002075 _141774 _141775) (@lem8002074 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8002078 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term124 _141774 _141775 _141776 P a b) = (term124 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8002077) (@lem8002076 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002079 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term126 _141774 _141775 _141776 P a b) = (term126 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8002078 _141774 _141775 _141776 P a b) (@lem8002043 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002112 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term196 _141774 _141775 _141776 x y P a b) = (term196 _141774 _141775 _141776 x y P a b).
Proof. exact (eq_refl (term196 _141774 _141775 _141776 x y P a b)). Qed.
Lemma lem8002113 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term198 _141774 _141775 _141776 x y P a b) = (term198 _141774 _141775 _141776 x y P a b).
Proof. exact (MK_COMB (@lem8002112 _141774 _141775 _141776 x y P a b) (@lem8002079 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002114 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term198 _141774 _141775 _141776 x y P a b) : term198 _141774 _141775 _141776 x y P a b.
Proof. exact (EQ_MP (@lem8002113 _141774 _141775 _141776 x y P a b) (@lem8002038 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002115 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term160 _141774 _141775 _141776 x y P a b.
Proof. exact (h1). Qed.
Lemma lem8002116 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term126 _141774 _141775 _141776 P a b.
Proof. exact (h1). Qed.
Lemma lem8002118 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term69 _141774 _141775 _141776 P a x b y.
Proof. exact (proj1 (@lem8002115 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002119 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term68 _141774 _141775 _141776 a x b y.
Proof. exact (proj2 (@lem8002118 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002124 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term121 _141774 _141775 _141776 P a b.
Proof. exact (proj1 (@lem8002116 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002154 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) (y : cart _141774 _141776) : (term104 _141774 _141775 _141776 P a x b y) = (term104 _141774 _141775 _141776 P a x b y).
Proof. exact (eq_refl (term104 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8002155 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term113 _141774 _141775 _141776 P a x b) = (term113 _141774 _141775 _141776 P a x b).
Proof. exact (fun_ext (fun y : cart _141774 _141776 => @lem8002154 _141774 _141775 _141776 P a x b y)). Qed.
Lemma lem8002156 {_141774 _141776 : Type'} : (@all (cart _141774 _141776)) = (@all (cart _141774 _141776)).
Proof. exact (eq_refl (@all (cart _141774 _141776))). Qed.
Lemma lem8002157 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (x : cart _141774 _141775) (b : cart _141774 _141776) : (term114 _141774 _141775 _141776 P a x b) = (term114 _141774 _141775 _141776 P a x b).
Proof. exact (MK_COMB (@lem8002156 _141774 _141776) (@lem8002155 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8002158 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term120 _141774 _141775 _141776 P a b) = (term120 _141774 _141775 _141776 P a b).
Proof. exact (fun_ext (fun x : cart _141774 _141775 => @lem8002157 _141774 _141775 _141776 P a x b)). Qed.
Lemma lem8002159 {_141774 _141775 : Type'} : (@all (cart _141774 _141775)) = (@all (cart _141774 _141775)).
Proof. exact (eq_refl (@all (cart _141774 _141775))). Qed.
Lemma lem8002161 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term121 _141774 _141775 _141776 P a b) = (term121 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8002159 _141774 _141775) (@lem8002158 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002162 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term121 _141774 _141775 _141776 P a b.
Proof. exact (EQ_MP (@lem8002161 _141774 _141775 _141776 P a b) (@lem8002124 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002167 {_141774 _141775 _141776 : Type'} (_105599 : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term204 _141774 _141775 _141776 P a b _105599.
Proof. exact (@lem8002162 _141774 _141775 _141776 P a b h1 _105599). Qed.
Lemma lem8002168 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) : (term204 _141774 _141775 _141776 P a b _105599) = (term114 _141774 _141775 _141776 P a _105599 b).
Proof. exact (eq_refl (term204 _141774 _141775 _141776 P a b _105599)). Qed.
Lemma lem8002169 {_141774 _141775 _141776 : Type'} (_105599 : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term114 _141774 _141775 _141776 P a _105599 b.
Proof. exact (EQ_MP (@lem8002168 _141774 _141775 _141776 P a _105599 b) (@lem8002167 _141774 _141775 _141776 _105599 P a b h1)). Qed.
Lemma lem8002170 {_141774 _141775 _141776 : Type'} (_105599 : cart _141774 _141775) (_105600 : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term205 _141774 _141775 _141776 P a _105599 b _105600.
Proof. exact (@lem8002169 _141774 _141775 _141776 _105599 P a b h1 _105600). Qed.
Lemma lem8002171 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) (_105600 : cart _141774 _141776) : (term205 _141774 _141775 _141776 P a _105599 b _105600) = (term104 _141774 _141775 _141776 P a _105599 b _105600).
Proof. exact (eq_refl (term205 _141774 _141775 _141776 P a _105599 b _105600)). Qed.
Lemma lem8002174 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term122 _141774 _141775 _141776 P a b.
Proof. exact (proj2 (@lem8002115 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002180 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : b = y.
Proof. exact (proj2 (@lem8002119 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002190 {_141774 _141775 _141776 : Type'} (_105599 : cart _141774 _141775) (_105600 : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term104 _141774 _141775 _141776 P a _105599 b _105600.
Proof. exact (EQ_MP (@lem8002171 _141774 _141775 _141776 P a _105599 b _105600) (@lem8002170 _141774 _141775 _141776 _105599 _105600 P a b h1)). Qed.
Lemma lem8002207 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : (term206 _141774 _141775 _141776 P a) = (term206 _141774 _141775 _141776 P a).
Proof. exact (eq_refl (term206 _141774 _141775 _141776 P a)). Qed.
Lemma lem8002208 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : (term207 _141774 _141775 _141776 P a b) = (term207 _141774 _141775 _141776 P a y).
Proof. exact (MK_COMB (@lem8002207 _141774 _141775 _141776 P a) (@lem8002180 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002209 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (y : cart _141774 _141776) : (term207 _141774 _141775 _141776 P a y) = (term122 _141774 _141775 _141776 P a y).
Proof. exact (eq_refl (term207 _141774 _141775 _141776 P a y)). Qed.
Lemma lem8002210 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term208 _141774 _141775 _141776 P a b) = (term208 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term208 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002211 {_141774 _141775 _141776 : Type'} (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (y : cart _141774 _141776) : ((term207 _141774 _141775 _141776 P a b) = (term207 _141774 _141775 _141776 P a y)) = ((term207 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a y)).
Proof. exact (MK_COMB (@lem8002210 _141774 _141775 _141776 P a b) (@lem8002209 _141774 _141775 _141776 P a y)). Qed.
Lemma lem8002212 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term207 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a b).
Proof. exact (eq_refl (term207 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8002214 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term208 _141774 _141775 _141776 P a b) = (term209 _141774 _141775 _141776 P a b).
Proof. exact (MK_COMB (@lem8002213) (@lem8002212 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002215 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (y : cart _141774 _141776) : (term122 _141774 _141775 _141776 P a y) = (term122 _141774 _141775 _141776 P a y).
Proof. exact (eq_refl (term122 _141774 _141775 _141776 P a y)). Qed.
Lemma lem8002216 {_141774 _141775 _141776 : Type'} (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (y : cart _141774 _141776) : ((term207 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a y)) = ((term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a y)).
Proof. exact (MK_COMB (@lem8002214 _141774 _141775 _141776 P a b) (@lem8002215 _141774 _141775 _141776 P a y)). Qed.
Lemma lem8002217 {_141774 _141775 _141776 : Type'} (b : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (y : cart _141774 _141776) : ((term207 _141774 _141775 _141776 P a b) = (term207 _141774 _141775 _141776 P a y)) = ((term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a y)).
Proof. exact (TRANS (@lem8002211 _141774 _141775 _141776 b P a y) (@lem8002216 _141774 _141775 _141776 b P a y)). Qed.
Lemma lem8002218 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : (term122 _141774 _141775 _141776 P a b) = (term122 _141774 _141775 _141776 P a y).
Proof. exact (EQ_MP (@lem8002217 _141774 _141775 _141776 b P a y) (@lem8002208 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002219 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term122 _141774 _141775 _141776 P a y.
Proof. exact (EQ_MP (@lem8002218 _141774 _141775 _141776 x y P a b h1) (@lem8002174 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002247 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : a = x.
Proof. exact (proj1 (@lem8002119 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002262 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (y : cart _141774 _141776) : (term210 _141774 _141775 _141776 P y) = (term210 _141774 _141775 _141776 P y).
Proof. exact (eq_refl (term210 _141774 _141775 _141776 P y)). Qed.
Lemma lem8002263 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : (term211 _141774 _141775 _141776 P y a) = (term211 _141774 _141775 _141776 P y x).
Proof. exact (MK_COMB (@lem8002262 _141774 _141775 _141776 P y) (@lem8002247 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002264 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term211 _141774 _141775 _141776 P y x) = (term122 _141774 _141775 _141776 P x y).
Proof. exact (eq_refl (term211 _141774 _141775 _141776 P y x)). Qed.
Lemma lem8002265 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (y : cart _141774 _141776) (a : cart _141774 _141775) : (term212 _141774 _141775 _141776 P y a) = (term212 _141774 _141775 _141776 P y a).
Proof. exact (eq_refl (term212 _141774 _141775 _141776 P y a)). Qed.
Lemma lem8002266 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : ((term211 _141774 _141775 _141776 P y a) = (term211 _141774 _141775 _141776 P y x)) = ((term211 _141774 _141775 _141776 P y a) = (term122 _141774 _141775 _141776 P x y)).
Proof. exact (MK_COMB (@lem8002265 _141774 _141775 _141776 P y a) (@lem8002264 _141774 _141775 _141776 P x y)). Qed.
Lemma lem8002267 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (y : cart _141774 _141776) : (term211 _141774 _141775 _141776 P y a) = (term122 _141774 _141775 _141776 P a y).
Proof. exact (eq_refl (term211 _141774 _141775 _141776 P y a)). Qed.
Lemma lem8002268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8002269 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (y : cart _141774 _141776) : (term212 _141774 _141775 _141776 P y a) = (term209 _141774 _141775 _141776 P a y).
Proof. exact (MK_COMB (@lem8002268) (@lem8002267 _141774 _141775 _141776 P a y)). Qed.
Lemma lem8002270 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term122 _141774 _141775 _141776 P x y) = (term122 _141774 _141775 _141776 P x y).
Proof. exact (eq_refl (term122 _141774 _141775 _141776 P x y)). Qed.
Lemma lem8002271 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : ((term211 _141774 _141775 _141776 P y a) = (term122 _141774 _141775 _141776 P x y)) = ((term122 _141774 _141775 _141776 P a y) = (term122 _141774 _141775 _141776 P x y)).
Proof. exact (MK_COMB (@lem8002269 _141774 _141775 _141776 P a y) (@lem8002270 _141774 _141775 _141776 P x y)). Qed.
Lemma lem8002272 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : ((term211 _141774 _141775 _141776 P y a) = (term211 _141774 _141775 _141776 P y x)) = ((term122 _141774 _141775 _141776 P a y) = (term122 _141774 _141775 _141776 P x y)).
Proof. exact (TRANS (@lem8002266 _141774 _141775 _141776 a P x y) (@lem8002271 _141774 _141775 _141776 a P x y)). Qed.
Lemma lem8002273 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : (term122 _141774 _141775 _141776 P a y) = (term122 _141774 _141775 _141776 P x y).
Proof. exact (EQ_MP (@lem8002272 _141774 _141775 _141776 a P x y) (@lem8002263 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002274 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term122 _141774 _141775 _141776 P x y.
Proof. exact (EQ_MP (@lem8002273 _141774 _141775 _141776 x y P a b h1) (@lem8002219 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002290 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : P x y.
Proof. exact (proj1 (@lem8002118 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002291 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term213 _141774 _141775 _141776 P x y.
Proof. exact (fun h0 : term122 _141774 _141775 _141776 P x y => @lem8002290 _141774 _141775 _141776 x y P a b h1). Qed.
Lemma lem8002293 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8002294 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term213 _141774 _141775 _141776 P x y) = (P x y).
Proof. exact (@lem8002293 (P x y)). Qed.
Lemma lem8002295 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : P x y.
Proof. exact (EQ_MP (@lem8002294 _141774 _141775 _141776 P x y) (@lem8002291 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002298 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8002300 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (x : cart _141774 _141775) (y : cart _141774 _141776) : (term122 _141774 _141775 _141776 P x y) = (term215 _141774 _141775 _141776 P x y).
Proof. exact (@lem8002298 (P x y)). Qed.
Lemma lem8002303 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term215 _141774 _141775 _141776 P x y.
Proof. exact (EQ_MP (@lem8002300 _141774 _141775 _141776 P x y) (@lem8002274 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002306 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : False.
Proof. exact (@lem8002303 _141774 _141775 _141776 x y P a b h1 (@lem8002295 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002307 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : term216.
Proof. exact (fun h0 : ~ False => @lem8002306 _141774 _141775 _141776 x y P a b h1). Qed.
Lemma lem8002309 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8002310 : term216 = False.
Proof. exact (@lem8002309 False). Qed.
Lemma lem8002336 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : P a b.
Proof. exact (proj2 (@lem8002116 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002337 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term213 _141774 _141775 _141776 P a b.
Proof. exact (fun h0 : term122 _141774 _141775 _141776 P a b => @lem8002336 _141774 _141775 _141776 P a b h1). Qed.
Lemma lem8002339 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8002340 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term213 _141774 _141775 _141776 P a b) = (P a b).
Proof. exact (@lem8002339 (P a b)). Qed.
Lemma lem8002341 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : P a b.
Proof. exact (EQ_MP (@lem8002340 _141774 _141775 _141776 P a b) (@lem8002337 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002343 {_141774 _141775 : Type'} (x : cart _141774 _141775) : x = x.
Proof. exact (@lem21386 (cart _141774 _141775) x). Qed.
Lemma lem8002344 {_141774 _141775 : Type'} (x : cart _141774 _141775) : x = x.
Proof. exact (@lem8002343 _141774 _141775 x). Qed.
Lemma lem8002345 {_141774 _141775 : Type'} (a : cart _141774 _141775) : a = a.
Proof. exact (@lem8002344 _141774 _141775 a). Qed.
Lemma lem8002346 {_141774 _141775 : Type'} (a : cart _141774 _141775) : term217 _141774 _141775 a.
Proof. exact (fun h0 : term218 _141774 _141775 a => @lem8002345 _141774 _141775 a). Qed.
Lemma lem8002348 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8002349 {_141774 _141775 : Type'} (a : cart _141774 _141775) : (term217 _141774 _141775 a) = (a = a).
Proof. exact (@lem8002348 (a = a)). Qed.
Lemma lem8002350 {_141774 _141775 : Type'} (a : cart _141774 _141775) : a = a.
Proof. exact (EQ_MP (@lem8002349 _141774 _141775 a) (@lem8002346 _141774 _141775 a)). Qed.
Lemma lem8002352 {_141774 _141776 : Type'} (x : cart _141774 _141776) : x = x.
Proof. exact (@lem21386 (cart _141774 _141776) x). Qed.
Lemma lem8002353 {_141774 _141776 : Type'} (x : cart _141774 _141776) : x = x.
Proof. exact (@lem8002352 _141774 _141776 x). Qed.
Lemma lem8002354 {_141774 _141776 : Type'} (b : cart _141774 _141776) : b = b.
Proof. exact (@lem8002353 _141774 _141776 b). Qed.
Lemma lem8002355 {_141774 _141776 : Type'} (b : cart _141774 _141776) : term217 _141774 _141776 b.
Proof. exact (fun h0 : term218 _141774 _141776 b => @lem8002354 _141774 _141776 b). Qed.
Lemma lem8002357 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8002358 {_141774 _141776 : Type'} (b : cart _141774 _141776) : (term217 _141774 _141776 b) = (b = b).
Proof. exact (@lem8002357 (b = b)). Qed.
Lemma lem8002359 {_141774 _141776 : Type'} (b : cart _141774 _141776) : b = b.
Proof. exact (EQ_MP (@lem8002358 _141774 _141776 b) (@lem8002355 _141774 _141776 b)). Qed.
Lemma lem8002361 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8002362 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) (_105600 : cart _141774 _141776) : (term101 _141774 _141775 _141776 a _105599 b _105600) = (term100 _141774 _141775 _141776 a _105599 b _105600).
Proof. exact (@lem8002361 (a = _105599) (b = _105600)). Qed.
Lemma lem8002363 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (_105599 : cart _141774 _141775) (_105600 : cart _141774 _141776) : (term102 _141774 _141775 _141776 P _105599 _105600) = (term102 _141774 _141775 _141776 P _105599 _105600).
Proof. exact (eq_refl (term102 _141774 _141775 _141776 P _105599 _105600)). Qed.
Lemma lem8002364 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) (_105600 : cart _141774 _141776) : (term104 _141774 _141775 _141776 P a _105599 b _105600) = (term103 _141774 _141775 _141776 P a _105599 b _105600).
Proof. exact (MK_COMB (@lem8002363 _141774 _141775 _141776 P _105599 _105600) (@lem8002362 _141774 _141775 _141776 a _105599 b _105600)). Qed.
Lemma lem8002366 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8002367 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) (_105600 : cart _141774 _141776) : (term103 _141774 _141775 _141776 P a _105599 b _105600) = (term105 _141774 _141775 _141776 P a _105599 b _105600).
Proof. exact (@lem8002366 (P _105599 _105600) (term68 _141774 _141775 _141776 a _105599 b _105600)). Qed.
Lemma lem8002368 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) (_105600 : cart _141774 _141776) : (term104 _141774 _141775 _141776 P a _105599 b _105600) = (term105 _141774 _141775 _141776 P a _105599 b _105600).
Proof. exact (TRANS (@lem8002364 _141774 _141775 _141776 P a _105599 b _105600) (@lem8002367 _141774 _141775 _141776 P a _105599 b _105600)). Qed.
Lemma lem8002370 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8002371 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) (_105600 : cart _141774 _141776) : (term105 _141774 _141775 _141776 P a _105599 b _105600) = (term221 _141774 _141775 _141776 P a _105599 b _105600).
Proof. exact (@lem8002370 (term69 _141774 _141775 _141776 P a _105599 b _105600)). Qed.
Lemma lem8002372 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (_105599 : cart _141774 _141775) (b : cart _141774 _141776) (_105600 : cart _141774 _141776) : (term104 _141774 _141775 _141776 P a _105599 b _105600) = (term221 _141774 _141775 _141776 P a _105599 b _105600).
Proof. exact (TRANS (@lem8002368 _141774 _141775 _141776 P a _105599 b _105600) (@lem8002371 _141774 _141775 _141776 P a _105599 b _105600)). Qed.
Lemma lem8002374 {_141774 _141775 _141776 : Type'} (a : cart _141774 _141775) (b : cart _141774 _141776) : term222 _141774 _141775 _141776 a b.
Proof. exact (conj (@lem8002350 _141774 _141775 a) (@lem8002359 _141774 _141776 b)). Qed.
Lemma lem8002375 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term223 _141774 _141775 _141776 P a b.
Proof. exact (conj (@lem8002341 _141774 _141775 _141776 P a b h1) (@lem8002374 _141774 _141775 _141776 a b)). Qed.
Lemma lem8002377 {_141774 _141775 _141776 : Type'} (_105599 : cart _141774 _141775) (_105600 : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term221 _141774 _141775 _141776 P a _105599 b _105600.
Proof. exact (EQ_MP (@lem8002372 _141774 _141775 _141776 P a _105599 b _105600) (@lem8002190 _141774 _141775 _141776 _105599 _105600 P a b h1)). Qed.
Lemma lem8002378 {_141774 _141775 _141776 : Type'} (_105599 : cart _141774 _141775) (_105600 : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term221 _141774 _141775 _141776 P a _105599 b _105600.
Proof. exact (@lem8002377 _141774 _141775 _141776 _105599 _105600 P a b h1). Qed.
Lemma lem8002379 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term224 _141774 _141775 _141776 P a b.
Proof. exact (@lem8002378 _141774 _141775 _141776 a b P a b h1). Qed.
Lemma lem8002382 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : False.
Proof. exact (@lem8002379 _141774 _141775 _141776 P a b h1 (@lem8002375 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002383 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : term216.
Proof. exact (fun h0 : ~ False => @lem8002382 _141774 _141775 _141776 P a b h1). Qed.
Lemma lem8002385 (p : Prop) : (term214 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8002386 : term216 = False.
Proof. exact (@lem8002385 False). Qed.
Lemma lem8002387 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term126 _141774 _141775 _141776 P a b) : False.
Proof. exact (EQ_MP (@lem8002386) (@lem8002383 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002389 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term160 _141774 _141775 _141776 x y P a b) : False.
Proof. exact (EQ_MP (@lem8002310) (@lem8002307 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002390 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term198 _141774 _141775 _141776 x y P a b) : False.
Proof. exact (or_elim (@lem8002114 _141774 _141775 _141776 x y P a b h1) (fun h0 : term160 _141774 _141775 _141776 x y P a b => @lem8002389 _141774 _141775 _141776 x y P a b h0) (fun h0 : term126 _141774 _141775 _141776 P a b => @lem8002387 _141774 _141775 _141776 P a b h0)). Qed.
Lemma lem8002391 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term198 _141774 _141775 _141776 x y P a b) : (term198 _141774 _141775 _141776 x y P a b) = False.
Proof. exact (prop_ext (fun h2 : term198 _141774 _141775 _141776 x y P a b => @lem8002390 _141774 _141775 _141776 x y P a b h1) (fun h2 : False => @lem8002114 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002392 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (y : cart _141774 _141776) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term198 _141774 _141775 _141776 x y P a b) : False.
Proof. exact (EQ_MP (@lem8002391 _141774 _141775 _141776 x y P a b h1) (@lem8002114 _141774 _141775 _141776 x y P a b h1)). Qed.
Lemma lem8002393 {_141774 _141775 _141776 : Type'} (x : cart _141774 _141775) (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term201 _141774 _141775 _141776 x P a b) : False.
Proof. exact (ex_elim (@lem8002037 _141774 _141775 _141776 x P a b h1) (fun y : cart _141774 _141776 => fun h0 : term200 _141774 _141775 _141776 x P a b y => @lem8002392 _141774 _141775 _141776 x y P a b h0)). Qed.
Lemma lem8002394 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term99 _141774 _141775 _141776 P a b) : False.
Proof. exact (ex_elim (@lem8002036 _141774 _141775 _141776 P a b h1) (fun x : cart _141774 _141775 => fun h0 : term202 _141774 _141775 _141776 P a b x => @lem8002393 _141774 _141775 _141776 x P a b h0)). Qed.
Lemma lem8002395 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term99 _141774 _141775 _141776 P a b) : (term99 _141774 _141775 _141776 P a b) = False.
Proof. exact (prop_ext (fun h2 : term99 _141774 _141775 _141776 P a b => @lem8002394 _141774 _141775 _141776 P a b h1) (fun h2 : False => @lem8001758 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002396 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) (h1 : term99 _141774 _141775 _141776 P a b) : False.
Proof. exact (EQ_MP (@lem8002395 _141774 _141775 _141776 P a b h1) (@lem8001758 _141774 _141775 _141776 P a b h1)). Qed.
Lemma lem8002397 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : term98 _141774 _141775 _141776 P a b.
Proof. exact (fun h0 : term99 _141774 _141775 _141776 P a b => @lem8002396 _141774 _141775 _141776 P a b h0). Qed.
Lemma lem8002398 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term76 _141774 _141775 _141776 P a b) = (P a b).
Proof. exact (EQ_MP (@lem8001757 _141774 _141775 _141776 P a b) (@lem8002397 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8002403 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : term81 _141774 _141775 _141776 P a.
Proof. exact (fun b : cart _141774 _141776 => @lem8002398 _141774 _141775 _141776 P a b). Qed.
Lemma lem8002408 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : term85 _141774 _141775 _141776 P.
Proof. exact (fun a : cart _141774 _141775 => @lem8002403 _141774 _141775 _141776 P a). Qed.
Lemma lem8002413 {_141774 _141775 _141776 : Type'} : term89 _141774 _141775 _141776.
Proof. exact (fun P : type22 _141774 _141775 _141776 => @lem8002408 _141774 _141775 _141776 P). Qed.
Lemma lem8002414 {_141774 _141775 _141776 : Type'} : term91 _141774 _141775 _141776.
Proof. exact (EQ_MP (@lem8001753 _141774 _141775 _141776) (@lem8002413 _141774 _141775 _141776)). Qed.
Lemma lem8002416 {_141774 _141775 _141776 : Type'} : term91 _141774 _141775 _141776.
Proof. exact (@lem8001608 _141774 _141775 _141776 (@lem8002414 _141774 _141775 _141776)). Qed.
Lemma lem8002417 {_141774 _141775 _141776 : Type'} (h1 : term92 _141774 _141775 _141776) : False.
Proof. exact (@lem8002416 _141774 _141775 _141776 (@lem8001592 _141774 _141775 _141776 h1)). Qed.
Lemma lem8002418 {_141774 _141775 _141776 : Type'} (h1 : term92 _141774 _141775 _141776) : (term92 _141774 _141775 _141776) = False.
Proof. exact (prop_ext (fun h2 : term92 _141774 _141775 _141776 => @lem8002417 _141774 _141775 _141776 h1) (fun h2 : False => @lem8001592 _141774 _141775 _141776 h1)). Qed.
Lemma lem8002419 {_141774 _141775 _141776 : Type'} (h1 : term92 _141774 _141775 _141776) : False.
Proof. exact (EQ_MP (@lem8002418 _141774 _141775 _141776 h1) (@lem8001592 _141774 _141775 _141776 h1)). Qed.
Lemma lem8002420 {_141774 _141775 _141776 : Type'} : term91 _141774 _141775 _141776.
Proof. exact (fun h0 : term92 _141774 _141775 _141776 => @lem8002419 _141774 _141775 _141776 h0). Qed.
Lemma lem8002421 {_141774 _141775 _141776 : Type'} : term89 _141774 _141775 _141776.
Proof. exact (EQ_MP (@lem8001591 _141774 _141775 _141776) (@lem8002420 _141774 _141775 _141776)). Qed.
Lemma lem8002422 {_141774 _141775 _141776 : Type'} : term88 _141774 _141775 _141776.
Proof. exact (EQ_MP (@lem8001587 _141774 _141775 _141776) (@lem8002421 _141774 _141775 _141776)). Qed.
