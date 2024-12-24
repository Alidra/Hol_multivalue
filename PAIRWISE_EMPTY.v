Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_EMPTY_term_abbrevs.
Require Import NOT_IN_EMPTY_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1844_spec.
Require Import thm1856_spec.
Require Import thm82_spec.
Lemma lem4794404 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4794405 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4794406 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4794405 A x) (@lem4794404 A x)). Qed.
Lemma lem4794407 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4794409 {_110510 : Type'} (s : _110510 -> Prop) : term3 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4794410 {_110510 : Type'} (s : _110510 -> Prop) : (term3 _110510 s) = (term4 _110510 s).
Proof. exact (eq_refl (term3 _110510 s)). Qed.
Lemma lem4794411 {_110510 : Type'} (s : _110510 -> Prop) : term4 _110510 s.
Proof. exact (EQ_MP (@lem4794410 _110510 s) (@lem4794409 _110510 s)). Qed.
Lemma lem4794412 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term5 _110510 s r.
Proof. exact (@lem4794411 _110510 s r). Qed.
Lemma lem4794413 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term5 _110510 s r) = ((@pairwise _110510 r s) = (term6 _110510 s r)).
Proof. exact (eq_refl (term5 _110510 s r)). Qed.
Lemma lem4794420 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4794421 {_110522 : Type'} (r : type1402 _110522) : ((@pairwise _110522 r (@EMPTY _110522)) = True) = (@pairwise _110522 r (@EMPTY _110522)).
Proof. exact (@lem4794420 (@pairwise _110522 r (@EMPTY _110522))). Qed.
Lemma lem4794423 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term6 _110510 s r).
Proof. exact (EQ_MP (@lem4794413 _110510 s r) (@lem4794412 _110510 s r)). Qed.
Lemma lem4794424 {_110522 : Type'} (s : _110522 -> Prop) (r : type1402 _110522) : (@pairwise _110522 r s) = (term6 _110522 s r).
Proof. exact (@lem4794423 _110522 s r). Qed.
Lemma lem4794425 {_110522 : Type'} (r : type1402 _110522) : (@pairwise _110522 r (@EMPTY _110522)) = (term7 _110522 r).
Proof. exact (@lem4794424 _110522 (@EMPTY _110522) r). Qed.
Lemma lem4794430 {_110522 : Type'} (r : type1402 _110522) : ((@pairwise _110522 r (@EMPTY _110522)) = True) = (term7 _110522 r).
Proof. exact (TRANS (@lem4794421 _110522 r) (@lem4794425 _110522 r)). Qed.
Lemma lem4794440 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4794407 A x (@lem4794406 A x)). Qed.
Lemma lem4794441 {_110522 : Type'} (x : _110522) : (@IN _110522 x (@EMPTY _110522)) = False.
Proof. exact (@lem4794440 _110522 x). Qed.
Lemma lem4794442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4794443 {_110522 : Type'} (x : _110522) : (term8 _110522 x) = (and False).
Proof. exact (MK_COMB (@lem4794442) (@lem4794441 _110522 x)). Qed.
Lemma lem4794447 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4794407 A x (@lem4794406 A x)). Qed.
Lemma lem4794448 {_110522 : Type'} (x : _110522) : (@IN _110522 x (@EMPTY _110522)) = False.
Proof. exact (@lem4794447 _110522 x). Qed.
Lemma lem4794449 {_110522 : Type'} (y : _110522) : (@IN _110522 y (@EMPTY _110522)) = False.
Proof. exact (@lem4794448 _110522 y). Qed.
Lemma lem4794450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4794451 {_110522 : Type'} (y : _110522) : (term8 _110522 y) = (and False).
Proof. exact (MK_COMB (@lem4794450) (@lem4794449 _110522 y)). Qed.
Lemma lem4794454 {_110522 : Type'} (x : _110522) (y : _110522) : (term9 _110522 x y) = (term9 _110522 x y).
Proof. exact (eq_refl (term9 _110522 x y)). Qed.
Lemma lem4794455 {_110522 : Type'} (x : _110522) (y : _110522) : (term10 _110522 x y) = (term11 _110522 x y).
Proof. exact (MK_COMB (@lem4794451 _110522 y) (@lem4794454 _110522 x y)). Qed.
Lemma lem4794457 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4794458 {_110522 : Type'} (x : _110522) (y : _110522) : (term11 _110522 x y) = False.
Proof. exact (@lem4794457 (term9 _110522 x y)). Qed.
Lemma lem4794459 {_110522 : Type'} (x : _110522) (y : _110522) : (term10 _110522 x y) = False.
Proof. exact (TRANS (@lem4794455 _110522 x y) (@lem4794458 _110522 x y)). Qed.
Lemma lem4794460 {_110522 : Type'} (x : _110522) (y : _110522) : (term12 _110522 x y) = (False /\ False).
Proof. exact (MK_COMB (@lem4794443 _110522 x) (@lem4794459 _110522 x y)). Qed.
Lemma lem4794462 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4794463 : (False /\ False) = False.
Proof. exact (@lem4794462 False). Qed.
Lemma lem4794464 {_110522 : Type'} (x : _110522) (y : _110522) : (term12 _110522 x y) = False.
Proof. exact (TRANS (@lem4794460 _110522 x y) (@lem4794463)). Qed.
Lemma lem4794465 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4794466 {_110522 : Type'} (x : _110522) (y : _110522) : (term13 _110522 x y) = (imp False).
Proof. exact (MK_COMB (@lem4794465) (@lem4794464 _110522 x y)). Qed.
Lemma lem4794467 {_110522 : Type'} (r : type1402 _110522) (x : _110522) (y : _110522) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4794468 {_110522 : Type'} (r : type1402 _110522) (x : _110522) (y : _110522) : (term14 _110522 r x y) = (term15 _110522 r x y).
Proof. exact (MK_COMB (@lem4794466 _110522 x y) (@lem4794467 _110522 r x y)). Qed.
Lemma lem4794470 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4794471 {_110522 : Type'} (r : type1402 _110522) (x : _110522) (y : _110522) : (term15 _110522 r x y) = True.
Proof. exact (@lem4794470 (r x y)). Qed.
Lemma lem4794472 {_110522 : Type'} (r : type1402 _110522) (x : _110522) (y : _110522) : (term14 _110522 r x y) = True.
Proof. exact (TRANS (@lem4794468 _110522 r x y) (@lem4794471 _110522 r x y)). Qed.
Lemma lem4794473 {_110522 : Type'} (r : type1402 _110522) (x : _110522) : (term16 _110522 r x) = (term17 _110522).
Proof. exact (fun_ext (fun y : _110522 => @lem4794472 _110522 r x y)). Qed.
Lemma lem4794474 {_110522 : Type'} : (@all _110522) = (@all _110522).
Proof. exact (eq_refl (@all _110522)). Qed.
Lemma lem4794475 {_110522 : Type'} (r : type1402 _110522) (x : _110522) : (term18 _110522 r x) = (term19 _110522).
Proof. exact (MK_COMB (@lem4794474 _110522) (@lem4794473 _110522 r x)). Qed.
Lemma lem4794477 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4794478 {_110522 : Type'} (t : Prop) : (term20 _110522 t) = t.
Proof. exact (@lem4794477 _110522 t). Qed.
Lemma lem4794479 {_110522 : Type'} : (term19 _110522) = True.
Proof. exact (@lem4794478 _110522 True). Qed.
Lemma lem4794480 {_110522 : Type'} (r : type1402 _110522) (x : _110522) : (term18 _110522 r x) = True.
Proof. exact (TRANS (@lem4794475 _110522 r x) (@lem4794479 _110522)). Qed.
Lemma lem4794481 {_110522 : Type'} (r : type1402 _110522) : (term21 _110522 r) = (term17 _110522).
Proof. exact (fun_ext (fun x : _110522 => @lem4794480 _110522 r x)). Qed.
Lemma lem4794482 {_110522 : Type'} : (@all _110522) = (@all _110522).
Proof. exact (eq_refl (@all _110522)). Qed.
Lemma lem4794483 {_110522 : Type'} (r : type1402 _110522) : (term7 _110522 r) = (term19 _110522).
Proof. exact (MK_COMB (@lem4794482 _110522) (@lem4794481 _110522 r)). Qed.
Lemma lem4794485 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4794486 {_110522 : Type'} (t : Prop) : (term20 _110522 t) = t.
Proof. exact (@lem4794485 _110522 t). Qed.
Lemma lem4794487 {_110522 : Type'} : (term19 _110522) = True.
Proof. exact (@lem4794486 _110522 True). Qed.
Lemma lem4794488 {_110522 : Type'} (r : type1402 _110522) : (term7 _110522 r) = True.
Proof. exact (TRANS (@lem4794483 _110522 r) (@lem4794487 _110522)). Qed.
Lemma lem4794489 {_110522 : Type'} (r : type1402 _110522) : ((@pairwise _110522 r (@EMPTY _110522)) = True) = True.
Proof. exact (TRANS (@lem4794430 _110522 r) (@lem4794488 _110522 r)). Qed.
Lemma lem4794490 {_110522 : Type'} : (term22 _110522) = (term23 _110522).
Proof. exact (fun_ext (fun r : type1402 _110522 => @lem4794489 _110522 r)). Qed.
Lemma lem4794491 {_110522 : Type'} : (@all (_110522 -> _110522 -> Prop)) = (@all (_110522 -> _110522 -> Prop)).
Proof. exact (eq_refl (@all (_110522 -> _110522 -> Prop))). Qed.
Lemma lem4794492 {_110522 : Type'} : (term24 _110522) = (term25 _110522).
Proof. exact (MK_COMB (@lem4794491 _110522) (@lem4794490 _110522)). Qed.
Lemma lem4794494 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4794495 {_110522 : Type'} (t : Prop) : (term26 _110522 t) = t.
Proof. exact (@lem4794494 (type1402 _110522) t). Qed.
Lemma lem4794496 {_110522 : Type'} : (term25 _110522) = True.
Proof. exact (@lem4794495 _110522 True). Qed.
Lemma lem4794497 {_110522 : Type'} : (term24 _110522) = True.
Proof. exact (TRANS (@lem4794492 _110522) (@lem4794496 _110522)). Qed.
Lemma lem4794498 {_110522 : Type'} : True = (term24 _110522).
Proof. exact (SYM (@lem4794497 _110522)). Qed.
Lemma lem4794499 {_110522 : Type'} : term24 _110522.
Proof. exact (EQ_MP (@lem4794498 _110522) (@lem0)). Qed.
