Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_IMAGE_term_abbrevs.
Require Import ITERATE_IMAGE_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7124409 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7124411 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7124412 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7124411 A B C h1 op). Qed.
Lemma lem7124413 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7124414 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7124413 A B C op) (@lem7124412 A B C op h1)). Qed.
Lemma lem7124415 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7124416 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7124414 A B C op h1 (@lem7124415 C op h2)). Qed.
Lemma lem7124417 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7124416 A B C op h0 h1). Qed.
Lemma lem7124418 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7124419 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7124417 A B C op h2 (@lem7124418 A B C h1)). Qed.
Lemma lem7124420 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7124419 A B C op h1 h0). Qed.
Lemma lem7124421 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7124420 A B C op h1). Qed.
Lemma lem7124422 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7124421 A B C h0). Qed.
Lemma lem7124423 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7124422 A B C (@lem5942955 A B C)). Qed.
Lemma lem7124424 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7124423 A B C op). Qed.
Lemma lem7124425 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7124468 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7124469 {_133152 : Type'} : (@sum _133152) = (@iterate real _133152 real_add).
Proof. exact (@lem7124468 _133152). Qed.
Lemma lem7124470 {_133152 _133176 : Type'} (f : _133176 -> _133152) (s : _133176 -> Prop) : (@IMAGE _133176 _133152 f s) = (@IMAGE _133176 _133152 f s).
Proof. exact (eq_refl (@IMAGE _133176 _133152 f s)). Qed.
Lemma lem7124471 {_133152 _133176 : Type'} (f : _133176 -> _133152) (s : _133176 -> Prop) : (term6 _133152 _133176 f s) = (term7 _133152 _133176 f s).
Proof. exact (MK_COMB (@lem7124469 _133152) (@lem7124470 _133152 _133176 f s)). Qed.
Lemma lem7124472 {_133152 : Type'} (g : _133152 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7124473 {_133152 _133176 : Type'} (f : _133176 -> _133152) (s : _133176 -> Prop) (g : _133152 -> real) : (term8 _133152 _133176 f s g) = (term9 _133152 _133176 f s g).
Proof. exact (MK_COMB (@lem7124471 _133152 _133176 f s) (@lem7124472 _133152 g)). Qed.
Lemma lem7124474 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124475 {_133152 _133176 : Type'} (f : _133176 -> _133152) (s : _133176 -> Prop) (g : _133152 -> real) : (term10 _133152 _133176 f s g) = (term11 _133152 _133176 f s g).
Proof. exact (MK_COMB (@lem7124474) (@lem7124473 _133152 _133176 f s g)). Qed.
Lemma lem7124477 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7124478 {_133176 : Type'} : (@sum _133176) = (@iterate real _133176 real_add).
Proof. exact (@lem7124477 _133176). Qed.
Lemma lem7124479 {_133176 : Type'} (s : _133176 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7124480 {_133176 : Type'} (s : _133176 -> Prop) : (@sum _133176 s) = (@iterate real _133176 real_add s).
Proof. exact (MK_COMB (@lem7124478 _133176) (@lem7124479 _133176 s)). Qed.
Lemma lem7124481 {_133152 _133176 : Type'} (g : _133152 -> real) (f : _133176 -> _133152) : (@o _133176 _133152 real g f) = (@o _133176 _133152 real g f).
Proof. exact (eq_refl (@o _133176 _133152 real g f)). Qed.
Lemma lem7124482 {_133152 _133176 : Type'} (s : _133176 -> Prop) (g : _133152 -> real) (f : _133176 -> _133152) : (term12 _133152 _133176 s g f) = (term13 _133152 _133176 s g f).
Proof. exact (MK_COMB (@lem7124480 _133176 s) (@lem7124481 _133152 _133176 g f)). Qed.
Lemma lem7124483 {_133152 _133176 : Type'} (s : _133176 -> Prop) (g : _133152 -> real) (f : _133176 -> _133152) : ((term8 _133152 _133176 f s g) = (term12 _133152 _133176 s g f)) = ((term9 _133152 _133176 f s g) = (term13 _133152 _133176 s g f)).
Proof. exact (MK_COMB (@lem7124475 _133152 _133176 f s g) (@lem7124482 _133152 _133176 s g f)). Qed.
Lemma lem7124486 {_133152 _133176 : Type'} (s : _133176 -> Prop) (f : _133176 -> _133152) : (term14 _133152 _133176 s f) = (term14 _133152 _133176 s f).
Proof. exact (eq_refl (term14 _133152 _133176 s f)). Qed.
Lemma lem7124487 {_133152 _133176 : Type'} (s : _133176 -> Prop) (g : _133152 -> real) (f : _133176 -> _133152) : (term15 _133152 _133176 s g f) = (term16 _133152 _133176 s g f).
Proof. exact (MK_COMB (@lem7124486 _133152 _133176 s f) (@lem7124483 _133152 _133176 s g f)). Qed.
Lemma lem7124490 {_133152 _133176 : Type'} (g : _133152 -> real) (f : _133176 -> _133152) : (term17 _133152 _133176 g f) = (term18 _133152 _133176 g f).
Proof. exact (fun_ext (fun s : _133176 -> Prop => @lem7124487 _133152 _133176 s g f)). Qed.
Lemma lem7124491 {_133176 : Type'} : (@all (_133176 -> Prop)) = (@all (_133176 -> Prop)).
Proof. exact (eq_refl (@all (_133176 -> Prop))). Qed.
Lemma lem7124492 {_133152 _133176 : Type'} (g : _133152 -> real) (f : _133176 -> _133152) : (term19 _133152 _133176 g f) = (term20 _133152 _133176 g f).
Proof. exact (MK_COMB (@lem7124491 _133176) (@lem7124490 _133152 _133176 g f)). Qed.
Lemma lem7124497 {_133152 _133176 : Type'} (f : _133176 -> _133152) : (term21 _133152 _133176 f) = (term22 _133152 _133176 f).
Proof. exact (fun_ext (fun g : _133152 -> real => @lem7124492 _133152 _133176 g f)). Qed.
Lemma lem7124498 {_133152 : Type'} : (@all (_133152 -> real)) = (@all (_133152 -> real)).
Proof. exact (eq_refl (@all (_133152 -> real))). Qed.
Lemma lem7124499 {_133152 _133176 : Type'} (f : _133176 -> _133152) : (term23 _133152 _133176 f) = (term24 _133152 _133176 f).
Proof. exact (MK_COMB (@lem7124498 _133152) (@lem7124497 _133152 _133176 f)). Qed.
Lemma lem7124504 {_133152 _133176 : Type'} : (term25 _133152 _133176) = (term26 _133152 _133176).
Proof. exact (fun_ext (fun f : _133176 -> _133152 => @lem7124499 _133152 _133176 f)). Qed.
Lemma lem7124505 {_133152 _133176 : Type'} : (@all (_133176 -> _133152)) = (@all (_133176 -> _133152)).
Proof. exact (eq_refl (@all (_133176 -> _133152))). Qed.
Lemma lem7124506 {_133152 _133176 : Type'} : (term27 _133152 _133176) = (term28 _133152 _133176).
Proof. exact (MK_COMB (@lem7124505 _133152 _133176) (@lem7124504 _133152 _133176)). Qed.
Lemma lem7124511 {_133152 _133176 : Type'} : (term28 _133152 _133176) = (term27 _133152 _133176).
Proof. exact (SYM (@lem7124506 _133152 _133176)). Qed.
Lemma lem7124513 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7124425 A B C op) (@lem7124424 A B C op)). Qed.
Lemma lem7124514 {_133152 _133176 : Type'} (op : type1627) : term29 _133152 _133176 op.
Proof. exact (@lem7124513 _133176 _133152 real op). Qed.
Lemma lem7124515 {_133152 _133176 : Type'} : term30 _133152 _133176.
Proof. exact (@lem7124514 _133152 _133176 real_add). Qed.
Lemma lem7124517 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7124409) (@lem7067132)). Qed.
Lemma lem7124518 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7124517)). Qed.
Lemma lem7124519 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7124518) (@lem0)). Qed.
Lemma lem7124520 {_133152 _133176 : Type'} : term28 _133152 _133176.
Proof. exact (@lem7124515 _133152 _133176 (@lem7124519)). Qed.
Lemma lem7124521 {_133152 _133176 : Type'} : term27 _133152 _133176.
Proof. exact (EQ_MP (@lem7124511 _133152 _133176) (@lem7124520 _133152 _133176)). Qed.
