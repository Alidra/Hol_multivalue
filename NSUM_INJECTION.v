Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_INJECTION_term_abbrevs.
Require Import ITERATE_INJECTION_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7018354 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7018356 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7018357 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7018356 A B h1 op). Qed.
Lemma lem7018358 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7018359 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7018358 A B op) (@lem7018357 A B op h1)). Qed.
Lemma lem7018360 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7018361 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7018359 A B op h1 (@lem7018360 B op h2)). Qed.
Lemma lem7018362 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7018361 A B op h0 h1). Qed.
Lemma lem7018363 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7018364 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7018362 A B op h2 (@lem7018363 A B h1)). Qed.
Lemma lem7018365 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7018364 A B op h1 h0). Qed.
Lemma lem7018366 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7018365 A B op h1). Qed.
Lemma lem7018367 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7018366 A B h0). Qed.
Lemma lem7018368 {A B : Type'} : term0 A B.
Proof. exact (@lem7018367 A B (@lem6003902 A B)). Qed.
Lemma lem7018369 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7018368 A B op). Qed.
Lemma lem7018370 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7018417 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018418 {_129571 : Type'} : (@nsum _129571) = (@iterate nat _129571 Nat.add).
Proof. exact (@lem7018417 _129571). Qed.
Lemma lem7018419 {_129571 : Type'} (s : _129571 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7018420 {_129571 : Type'} (s : _129571 -> Prop) : (@nsum _129571 s) = (@iterate nat _129571 Nat.add s).
Proof. exact (MK_COMB (@lem7018418 _129571) (@lem7018419 _129571 s)). Qed.
Lemma lem7018421 {_129571 : Type'} (f : _129571 -> nat) (p : _129571 -> _129571) : (@o _129571 _129571 nat f p) = (@o _129571 _129571 nat f p).
Proof. exact (eq_refl (@o _129571 _129571 nat f p)). Qed.
Lemma lem7018422 {_129571 : Type'} (s : _129571 -> Prop) (f : _129571 -> nat) (p : _129571 -> _129571) : (term6 _129571 s f p) = (term7 _129571 s f p).
Proof. exact (MK_COMB (@lem7018420 _129571 s) (@lem7018421 _129571 f p)). Qed.
Lemma lem7018423 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7018424 {_129571 : Type'} (s : _129571 -> Prop) (f : _129571 -> nat) (p : _129571 -> _129571) : (term8 _129571 s f p) = (term9 _129571 s f p).
Proof. exact (MK_COMB (@lem7018423) (@lem7018422 _129571 s f p)). Qed.
Lemma lem7018426 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018427 {_129571 : Type'} : (@nsum _129571) = (@iterate nat _129571 Nat.add).
Proof. exact (@lem7018426 _129571). Qed.
Lemma lem7018428 {_129571 : Type'} (s : _129571 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7018429 {_129571 : Type'} (s : _129571 -> Prop) : (@nsum _129571 s) = (@iterate nat _129571 Nat.add s).
Proof. exact (MK_COMB (@lem7018427 _129571) (@lem7018428 _129571 s)). Qed.
Lemma lem7018430 {_129571 : Type'} (f : _129571 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018431 {_129571 : Type'} (s : _129571 -> Prop) (f : _129571 -> nat) : (@nsum _129571 s f) = (@iterate nat _129571 Nat.add s f).
Proof. exact (MK_COMB (@lem7018429 _129571 s) (@lem7018430 _129571 f)). Qed.
Lemma lem7018432 {_129571 : Type'} (p : _129571 -> _129571) (s : _129571 -> Prop) (f : _129571 -> nat) : ((term6 _129571 s f p) = (@nsum _129571 s f)) = ((term7 _129571 s f p) = (@iterate nat _129571 Nat.add s f)).
Proof. exact (MK_COMB (@lem7018424 _129571 s f p) (@lem7018431 _129571 s f)). Qed.
Lemma lem7018435 {_129571 : Type'} (s : _129571 -> Prop) (p : _129571 -> _129571) : (term10 _129571 s p) = (term10 _129571 s p).
Proof. exact (eq_refl (term10 _129571 s p)). Qed.
Lemma lem7018436 {_129571 : Type'} (p : _129571 -> _129571) (s : _129571 -> Prop) (f : _129571 -> nat) : (term11 _129571 p s f) = (term12 _129571 p s f).
Proof. exact (MK_COMB (@lem7018435 _129571 s p) (@lem7018432 _129571 p s f)). Qed.
Lemma lem7018439 {_129571 : Type'} (p : _129571 -> _129571) (f : _129571 -> nat) : (term13 _129571 p f) = (term14 _129571 p f).
Proof. exact (fun_ext (fun s : _129571 -> Prop => @lem7018436 _129571 p s f)). Qed.
Lemma lem7018440 {_129571 : Type'} : (@all (_129571 -> Prop)) = (@all (_129571 -> Prop)).
Proof. exact (eq_refl (@all (_129571 -> Prop))). Qed.
Lemma lem7018441 {_129571 : Type'} (p : _129571 -> _129571) (f : _129571 -> nat) : (term15 _129571 p f) = (term16 _129571 p f).
Proof. exact (MK_COMB (@lem7018440 _129571) (@lem7018439 _129571 p f)). Qed.
Lemma lem7018446 {_129571 : Type'} (f : _129571 -> nat) : (term17 _129571 f) = (term18 _129571 f).
Proof. exact (fun_ext (fun p : _129571 -> _129571 => @lem7018441 _129571 p f)). Qed.
Lemma lem7018447 {_129571 : Type'} : (@all (_129571 -> _129571)) = (@all (_129571 -> _129571)).
Proof. exact (eq_refl (@all (_129571 -> _129571))). Qed.
Lemma lem7018448 {_129571 : Type'} (f : _129571 -> nat) : (term19 _129571 f) = (term20 _129571 f).
Proof. exact (MK_COMB (@lem7018447 _129571) (@lem7018446 _129571 f)). Qed.
Lemma lem7018453 {_129571 : Type'} : (term21 _129571) = (term22 _129571).
Proof. exact (fun_ext (fun f : _129571 -> nat => @lem7018448 _129571 f)). Qed.
Lemma lem7018454 {_129571 : Type'} : (@all (_129571 -> nat)) = (@all (_129571 -> nat)).
Proof. exact (eq_refl (@all (_129571 -> nat))). Qed.
Lemma lem7018455 {_129571 : Type'} : (term23 _129571) = (term24 _129571).
Proof. exact (MK_COMB (@lem7018454 _129571) (@lem7018453 _129571)). Qed.
Lemma lem7018460 {_129571 : Type'} : (term24 _129571) = (term23 _129571).
Proof. exact (SYM (@lem7018455 _129571)). Qed.
Lemma lem7018462 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7018370 A B op) (@lem7018369 A B op)). Qed.
Lemma lem7018463 {_129571 : Type'} (op : type1606) : term25 _129571 op.
Proof. exact (@lem7018462 _129571 nat op). Qed.
Lemma lem7018464 {_129571 : Type'} : term26 _129571.
Proof. exact (@lem7018463 _129571 Nat.add). Qed.
Lemma lem7018466 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7018354) (@lem6924403)). Qed.
Lemma lem7018467 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7018466)). Qed.
Lemma lem7018468 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7018467) (@lem0)). Qed.
Lemma lem7018469 {_129571 : Type'} : term24 _129571.
Proof. exact (@lem7018464 _129571 (@lem7018468)). Qed.
Lemma lem7018470 {_129571 : Type'} : term23 _129571.
Proof. exact (EQ_MP (@lem7018460 _129571) (@lem7018469 _129571)). Qed.
