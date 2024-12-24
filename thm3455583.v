Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3455583_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3453857_spec.
Lemma lem3454376 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3454377 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term1 _89520 _89534 P f) = (term2 _89520 _89534 P f).
Proof. exact (@lem3454376 (term1 _89520 _89534 P f)). Qed.
Lemma lem3454378 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term2 _89520 _89534 P f) = (term1 _89520 _89534 P f).
Proof. exact (SYM (@lem3454377 _89520 _89534 P f)). Qed.
Lemma lem3454379 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term3 _89520 _89534 P f) : term3 _89520 _89534 P f.
Proof. exact (h1). Qed.
Lemma lem3454382 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term2 _89520 _89534 P f) : term2 _89520 _89534 P f.
Proof. exact (h1). Qed.
Lemma lem3454383 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term4 _89520 _89534 P f.
Proof. exact (fun h0 : term2 _89520 _89534 P f => @lem3454382 _89520 _89534 P f h0). Qed.
Lemma lem3454384 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term4 _89520 _89534 P f) : term4 _89520 _89534 P f.
Proof. exact (h1). Qed.
Lemma lem3454385 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term2 _89520 _89534 P f) : term2 _89520 _89534 P f.
Proof. exact (h1). Qed.
Lemma lem3454386 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term2 _89520 _89534 P f) (h2 : term4 _89520 _89534 P f) : term2 _89520 _89534 P f.
Proof. exact (@lem3454384 _89520 _89534 P f h2 (@lem3454385 _89520 _89534 P f h1)). Qed.
Lemma lem3454387 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term2 _89520 _89534 P f) : term5 _89520 _89534 P f.
Proof. exact (fun h0 : term4 _89520 _89534 P f => @lem3454386 _89520 _89534 P f h1 h0). Qed.
Lemma lem3454388 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term4 _89520 _89534 P f) : term4 _89520 _89534 P f.
Proof. exact (h1). Qed.
Lemma lem3454389 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term2 _89520 _89534 P f) (h2 : term4 _89520 _89534 P f) : term2 _89520 _89534 P f.
Proof. exact (@lem3454387 _89520 _89534 P f h1 (@lem3454388 _89520 _89534 P f h2)). Qed.
Lemma lem3454390 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term4 _89520 _89534 P f) : term4 _89520 _89534 P f.
Proof. exact (fun h0 : term2 _89520 _89534 P f => @lem3454389 _89520 _89534 P f h0 h1). Qed.
Lemma lem3454391 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term6 _89520 _89534 P f.
Proof. exact (fun h0 : term4 _89520 _89534 P f => @lem3454390 _89520 _89534 P f h0). Qed.
Lemma lem3454394 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term4 _89520 _89534 P f.
Proof. exact (@lem3454391 _89520 _89534 P f (@lem3454383 _89520 _89534 P f)). Qed.
Lemma lem3454395 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term4 _89520 _89534 P f.
Proof. exact (@lem3454394 _89520 _89534 P f). Qed.
Lemma lem3454405 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3454406 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term2 _89520 _89534 P f) = (term7 _89520 _89534 P f).
Proof. exact (@lem3454405 (term3 _89520 _89534 P f)). Qed.
Lemma lem3454408 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3454409 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term7 _89520 _89534 P f) = (term1 _89520 _89534 P f).
Proof. exact (@lem3454408 (term1 _89520 _89534 P f)). Qed.
Lemma lem3454414 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term2 _89520 _89534 P f) = (term1 _89520 _89534 P f).
Proof. exact (TRANS (@lem3454406 _89520 _89534 P f) (@lem3454409 _89520 _89534 P f)). Qed.
Lemma lem3454525 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : (term9 _89520 _89534 f) = (term10 _89520 _89534 f).
Proof. exact (fun_ext (fun P : _89534 -> Prop => @lem3454414 _89520 _89534 P f)). Qed.
Lemma lem3454526 {_89534 : Type'} : (@all (_89534 -> Prop)) = (@all (_89534 -> Prop)).
Proof. exact (eq_refl (@all (_89534 -> Prop))). Qed.
Lemma lem3454527 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : (term11 _89520 _89534 f) = (term12 _89520 _89534 f).
Proof. exact (MK_COMB (@lem3454526 _89534) (@lem3454525 _89520 _89534 f)). Qed.
Lemma lem3454532 {_89520 _89534 : Type'} : (term13 _89520 _89534) = (term14 _89520 _89534).
Proof. exact (fun_ext (fun f : type1470 _89520 _89534 => @lem3454527 _89520 _89534 f)). Qed.
Lemma lem3454533 {_89520 _89534 : Type'} : (@all (_89534 -> _89520 -> Prop)) = (@all (_89534 -> _89520 -> Prop)).
Proof. exact (eq_refl (@all (_89534 -> _89520 -> Prop))). Qed.
Lemma lem3454542 {_89520 _89534 : Type'} : (term15 _89520 _89534) = (term16 _89520 _89534).
Proof. exact (MK_COMB (@lem3454533 _89520 _89534) (@lem3454532 _89520 _89534)). Qed.
Lemma lem3454547 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term17 _89520 _89534 P x f x') = (term17 _89520 _89534 P x f x').
Proof. exact (eq_refl (term17 _89520 _89534 P x f x')). Qed.
Lemma lem3454548 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term18 _89520 _89534 P x f) = (term18 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3454547 _89520 _89534 P x f x')). Qed.
Lemma lem3454549 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3454550 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term19 _89520 _89534 P x f) = (term19 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454549 _89534) (@lem3454548 _89520 _89534 P x f)). Qed.
Lemma lem3454551 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (@IN _89520 x t) = (@IN _89520 x t).
Proof. exact (eq_refl (@IN _89520 x t)). Qed.
Lemma lem3454556 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term20 _89520 _89534 P t f x) = (term20 _89520 _89534 P t f x).
Proof. exact (eq_refl (term20 _89520 _89534 P t f x)). Qed.
Lemma lem3454557 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term21 _89520 _89534 P t f) = (term21 _89520 _89534 P t f).
Proof. exact (fun_ext (fun x : _89534 => @lem3454556 _89520 _89534 P t f x)). Qed.
Lemma lem3454558 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3454559 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term22 _89520 _89534 P t f) = (term22 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454558 _89534) (@lem3454557 _89520 _89534 P t f)). Qed.
Lemma lem3454560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454561 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term23 _89520 _89534 P t f) = (term23 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454560) (@lem3454559 _89520 _89534 P t f)). Qed.
Lemma lem3454562 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term24 _89520 _89534 P f x t) = (term24 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454561 _89520 _89534 P t f) (@lem3454551 _89520 x t)). Qed.
Lemma lem3454563 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term25 _89520 _89534 P f x) = (term25 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3454562 _89520 _89534 P f x t)). Qed.
Lemma lem3454564 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3454565 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term26 _89520 _89534 P f x) = (term26 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454564 _89520) (@lem3454563 _89520 _89534 P f x)). Qed.
Lemma lem3454566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454567 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term27 _89520 _89534 P f x) = (term27 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454566) (@lem3454565 _89520 _89534 P f x)). Qed.
Lemma lem3454568 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term26 _89520 _89534 P f x) = (term19 _89520 _89534 P x f)) = ((term26 _89520 _89534 P f x) = (term19 _89520 _89534 P x f)).
Proof. exact (MK_COMB (@lem3454567 _89520 _89534 P f x) (@lem3454550 _89520 _89534 P x f)). Qed.
Lemma lem3454569 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term28 _89520 _89534 P f) = (term28 _89520 _89534 P f).
Proof. exact (fun_ext (fun x : _89520 => @lem3454568 _89520 _89534 P x f)). Qed.
Lemma lem3454570 {_89520 : Type'} : (@all _89520) = (@all _89520).
Proof. exact (eq_refl (@all _89520)). Qed.
Lemma lem3454571 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term1 _89520 _89534 P f) = (term1 _89520 _89534 P f).
Proof. exact (MK_COMB (@lem3454570 _89520) (@lem3454569 _89520 _89534 P f)). Qed.
Lemma lem3454572 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : (term10 _89520 _89534 f) = (term10 _89520 _89534 f).
Proof. exact (fun_ext (fun P : _89534 -> Prop => @lem3454571 _89520 _89534 P f)). Qed.
Lemma lem3454573 {_89534 : Type'} : (@all (_89534 -> Prop)) = (@all (_89534 -> Prop)).
Proof. exact (eq_refl (@all (_89534 -> Prop))). Qed.
Lemma lem3454574 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : (term12 _89520 _89534 f) = (term12 _89520 _89534 f).
Proof. exact (MK_COMB (@lem3454573 _89534) (@lem3454572 _89520 _89534 f)). Qed.
Lemma lem3454575 {_89520 _89534 : Type'} : (term14 _89520 _89534) = (term14 _89520 _89534).
Proof. exact (fun_ext (fun f : type1470 _89520 _89534 => @lem3454574 _89520 _89534 f)). Qed.
Lemma lem3454576 {_89520 _89534 : Type'} : (@all (_89534 -> _89520 -> Prop)) = (@all (_89534 -> _89520 -> Prop)).
Proof. exact (eq_refl (@all (_89534 -> _89520 -> Prop))). Qed.
Lemma lem3454577 {_89520 _89534 : Type'} : (term16 _89520 _89534) = (term16 _89520 _89534).
Proof. exact (MK_COMB (@lem3454576 _89520 _89534) (@lem3454575 _89520 _89534)). Qed.
Lemma lem3454622 {_89520 _89534 : Type'} : (term15 _89520 _89534) = (term16 _89520 _89534).
Proof. exact (TRANS (@lem3454542 _89520 _89534) (@lem3454577 _89520 _89534)). Qed.
Lemma lem3454623 {_89520 _89534 : Type'} : (term16 _89520 _89534) = (term15 _89520 _89534).
Proof. exact (SYM (@lem3454622 _89520 _89534)). Qed.
Lemma lem3454625 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3454626 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term26 _89520 _89534 P f x) = (term19 _89520 _89534 P x f)) = (term29 _89520 _89534 P x f).
Proof. exact (@lem3454625 ((term26 _89520 _89534 P f x) = (term19 _89520 _89534 P x f))). Qed.
Lemma lem3454627 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term29 _89520 _89534 P x f) = ((term26 _89520 _89534 P f x) = (term19 _89520 _89534 P x f)).
Proof. exact (SYM (@lem3454626 _89520 _89534 P x f)). Qed.
Lemma lem3454628 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term30 _89520 _89534 P x f) : term30 _89520 _89534 P x f.
Proof. exact (h1). Qed.
Lemma lem3454637 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term31 _89520 _89534 P t f x) = (term32 _89520 _89534 P t f x).
Proof. exact (@lem17045 (P x) (t = (f x))). Qed.
Lemma lem3454640 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term20 _89520 _89534 P t f x) = (term20 _89520 _89534 P t f x).
Proof. exact (eq_refl (term20 _89520 _89534 P t f x)). Qed.
Lemma lem3454641 {_89534 : Type'} (P : _89534 -> Prop) : (term33 _89534 P) = (term34 _89534 P).
Proof. exact (@lem18394 _89534 P). Qed.
Lemma lem3454642 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term35 _89520 _89534 P t f) = (term36 _89520 _89534 P t f).
Proof. exact (@lem3454641 _89534 (term21 _89520 _89534 P t f)). Qed.
Lemma lem3454643 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term37 _89520 _89534 P t f x) = (term20 _89520 _89534 P t f x).
Proof. exact (eq_refl (term37 _89520 _89534 P t f x)). Qed.
Lemma lem3454644 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3454645 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term38 _89520 _89534 P t f x) = (term31 _89520 _89534 P t f x).
Proof. exact (MK_COMB (@lem3454644) (@lem3454643 _89520 _89534 P t f x)). Qed.
Lemma lem3454646 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term38 _89520 _89534 P t f x) = (term32 _89520 _89534 P t f x).
Proof. exact (TRANS (@lem3454645 _89520 _89534 P t f x) (@lem3454637 _89520 _89534 P t f x)). Qed.
Lemma lem3454647 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term39 _89520 _89534 P t f) = (term40 _89520 _89534 P t f).
Proof. exact (fun_ext (fun x : _89534 => @lem3454646 _89520 _89534 P t f x)). Qed.
Lemma lem3454648 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3454649 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term36 _89520 _89534 P t f) = (term41 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454648 _89534) (@lem3454647 _89520 _89534 P t f)). Qed.
Lemma lem3454650 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term35 _89520 _89534 P t f) = (term41 _89520 _89534 P t f).
Proof. exact (TRANS (@lem3454642 _89520 _89534 P t f) (@lem3454649 _89520 _89534 P t f)). Qed.
Lemma lem3454651 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term21 _89520 _89534 P t f) = (term21 _89520 _89534 P t f).
Proof. exact (fun_ext (fun x : _89534 => @lem3454640 _89520 _89534 P t f x)). Qed.
Lemma lem3454652 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3454653 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term22 _89520 _89534 P t f) = (term22 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454652 _89534) (@lem3454651 _89520 _89534 P t f)). Qed.
Lemma lem3454654 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (term42 _89520 x t) = (term42 _89520 x t).
Proof. exact (eq_refl (term42 _89520 x t)). Qed.
Lemma lem3454655 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (@IN _89520 x t) = (@IN _89520 x t).
Proof. exact (eq_refl (@IN _89520 x t)). Qed.
Lemma lem3454656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3454657 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term43 _89520 _89534 P t f) = (term44 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454656) (@lem3454650 _89520 _89534 P t f)). Qed.
Lemma lem3454658 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term45 _89520 _89534 P f x t) = (term46 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454657 _89520 _89534 P t f) (@lem3454654 _89520 x t)). Qed.
Lemma lem3454659 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term47 _89520 _89534 P f x t) = (term45 _89520 _89534 P f x t).
Proof. exact (@lem17045 (term22 _89520 _89534 P t f) (@IN _89520 x t)). Qed.
Lemma lem3454660 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term47 _89520 _89534 P f x t) = (term46 _89520 _89534 P f x t).
Proof. exact (TRANS (@lem3454659 _89520 _89534 P f x t) (@lem3454658 _89520 _89534 P f x t)). Qed.
Lemma lem3454661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454662 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term23 _89520 _89534 P t f) = (term23 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454661) (@lem3454653 _89520 _89534 P t f)). Qed.
Lemma lem3454663 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term24 _89520 _89534 P f x t) = (term24 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454662 _89520 _89534 P t f) (@lem3454655 _89520 x t)). Qed.
Lemma lem3454664 {_89520 : Type'} (P : type686 _89520) : (term48 _89520 P) = (term49 _89520 P).
Proof. exact (@lem18394 (_89520 -> Prop) P). Qed.
Lemma lem3454665 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term50 _89520 _89534 P f x) = (term51 _89520 _89534 P f x).
Proof. exact (@lem3454664 _89520 (term25 _89520 _89534 P f x)). Qed.
Lemma lem3454666 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term52 _89520 _89534 P f x t) = (term24 _89520 _89534 P f x t).
Proof. exact (eq_refl (term52 _89520 _89534 P f x t)). Qed.
Lemma lem3454667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3454668 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term53 _89520 _89534 P f x t) = (term47 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454667) (@lem3454666 _89520 _89534 P f x t)). Qed.
Lemma lem3454669 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term53 _89520 _89534 P f x t) = (term46 _89520 _89534 P f x t).
Proof. exact (TRANS (@lem3454668 _89520 _89534 P f x t) (@lem3454660 _89520 _89534 P f x t)). Qed.
Lemma lem3454670 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term54 _89520 _89534 P f x) = (term55 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3454669 _89520 _89534 P f x t)). Qed.
Lemma lem3454671 {_89520 : Type'} : (@all (_89520 -> Prop)) = (@all (_89520 -> Prop)).
Proof. exact (eq_refl (@all (_89520 -> Prop))). Qed.
Lemma lem3454672 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term51 _89520 _89534 P f x) = (term56 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454671 _89520) (@lem3454670 _89520 _89534 P f x)). Qed.
Lemma lem3454673 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term50 _89520 _89534 P f x) = (term56 _89520 _89534 P f x).
Proof. exact (TRANS (@lem3454665 _89520 _89534 P f x) (@lem3454672 _89520 _89534 P f x)). Qed.
Lemma lem3454674 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term25 _89520 _89534 P f x) = (term25 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3454663 _89520 _89534 P f x t)). Qed.
Lemma lem3454675 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3454676 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term26 _89520 _89534 P f x) = (term26 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454675 _89520) (@lem3454674 _89520 _89534 P f x)). Qed.
Lemma lem3454685 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term57 _89520 _89534 P x f x') = (term58 _89520 _89534 P x f x').
Proof. exact (@lem17045 (P x') (term59 _89520 _89534 x f x')). Qed.
Lemma lem3454688 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term17 _89520 _89534 P x f x') = (term17 _89520 _89534 P x f x').
Proof. exact (eq_refl (term17 _89520 _89534 P x f x')). Qed.
Lemma lem3454689 {_89534 : Type'} (P : _89534 -> Prop) : (term33 _89534 P) = (term34 _89534 P).
Proof. exact (@lem18394 _89534 P). Qed.
Lemma lem3454690 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term60 _89520 _89534 P x f) = (term61 _89520 _89534 P x f).
Proof. exact (@lem3454689 _89534 (term18 _89520 _89534 P x f)). Qed.
Lemma lem3454691 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term62 _89520 _89534 P x f x') = (term17 _89520 _89534 P x f x').
Proof. exact (eq_refl (term62 _89520 _89534 P x f x')). Qed.
Lemma lem3454692 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3454693 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term63 _89520 _89534 P x f x') = (term57 _89520 _89534 P x f x').
Proof. exact (MK_COMB (@lem3454692) (@lem3454691 _89520 _89534 P x f x')). Qed.
Lemma lem3454694 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term63 _89520 _89534 P x f x') = (term58 _89520 _89534 P x f x').
Proof. exact (TRANS (@lem3454693 _89520 _89534 P x f x') (@lem3454685 _89520 _89534 P x f x')). Qed.
Lemma lem3454695 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term64 _89520 _89534 P x f) = (term65 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3454694 _89520 _89534 P x f x')). Qed.
Lemma lem3454696 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3454697 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term61 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454696 _89534) (@lem3454695 _89520 _89534 P x f)). Qed.
Lemma lem3454698 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term60 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (TRANS (@lem3454690 _89520 _89534 P x f) (@lem3454697 _89520 _89534 P x f)). Qed.
Lemma lem3454699 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term18 _89520 _89534 P x f) = (term18 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3454688 _89520 _89534 P x f x')). Qed.
Lemma lem3454700 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3454701 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term19 _89520 _89534 P x f) = (term19 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454700 _89534) (@lem3454699 _89520 _89534 P x f)). Qed.
Lemma lem3454702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454703 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term67 _89520 _89534 P f x) = (term68 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454702) (@lem3454673 _89520 _89534 P f x)). Qed.
Lemma lem3454704 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term69 _89520 _89534 P x f) = (term70 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454703 _89520 _89534 P f x) (@lem3454701 _89520 _89534 P x f)). Qed.
Lemma lem3454705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454706 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term71 _89520 _89534 P f x) = (term71 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454705) (@lem3454676 _89520 _89534 P f x)). Qed.
Lemma lem3454707 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term72 _89520 _89534 P x f) = (term73 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454706 _89520 _89534 P f x) (@lem3454698 _89520 _89534 P x f)). Qed.
Lemma lem3454708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3454709 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term74 _89520 _89534 P x f) = (term75 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454708) (@lem3454707 _89520 _89534 P x f)). Qed.
Lemma lem3454710 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term76 _89520 _89534 P x f) = (term77 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454709 _89520 _89534 P x f) (@lem3454704 _89520 _89534 P x f)). Qed.
Lemma lem3454711 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term30 _89520 _89534 P x f) = (term76 _89520 _89534 P x f).
Proof. exact (@lem17646 (term26 _89520 _89534 P f x) (term19 _89520 _89534 P x f)). Qed.
Lemma lem3454712 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term30 _89520 _89534 P x f) = (term77 _89520 _89534 P x f).
Proof. exact (TRANS (@lem3454711 _89520 _89534 P x f) (@lem3454710 _89520 _89534 P x f)). Qed.
Lemma lem3454963 {A : Type'} (P : A -> Prop) (Q : Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3454964 {_89534 : Type'} (P : _89534 -> Prop) (Q : Prop) : (term78 _89534 P Q) = (term79 _89534 P Q).
Proof. exact (@lem3454963 _89534 P Q). Qed.
Lemma lem3454965 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term80 _89520 _89534 P f x t) = (term81 _89520 _89534 P f x t).
Proof. exact (@lem3454964 _89534 (term21 _89520 _89534 P t f) (@IN _89520 x t)). Qed.
Lemma lem3454966 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term37 _89520 _89534 P t f x) = (term20 _89520 _89534 P t f x).
Proof. exact (eq_refl (term37 _89520 _89534 P t f x)). Qed.
Lemma lem3454967 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term82 _89520 _89534 P t f) = (term21 _89520 _89534 P t f).
Proof. exact (fun_ext (fun x : _89534 => @lem3454966 _89520 _89534 P t f x)). Qed.
Lemma lem3454968 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3454969 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term83 _89520 _89534 P t f) = (term22 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454968 _89534) (@lem3454967 _89520 _89534 P t f)). Qed.
Lemma lem3454970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454971 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term84 _89520 _89534 P t f) = (term23 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3454970) (@lem3454969 _89520 _89534 P t f)). Qed.
Lemma lem3454972 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (@IN _89520 x t) = (@IN _89520 x t).
Proof. exact (eq_refl (@IN _89520 x t)). Qed.
Lemma lem3454973 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term80 _89520 _89534 P f x t) = (term24 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454971 _89520 _89534 P t f) (@lem3454972 _89520 x t)). Qed.
Lemma lem3454974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454975 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term85 _89520 _89534 P f x t) = (term86 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454974) (@lem3454973 _89520 _89534 P f x t)). Qed.
Lemma lem3454976 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term37 _89520 _89534 P t f x) = (term20 _89520 _89534 P t f x).
Proof. exact (eq_refl (term37 _89520 _89534 P t f x)). Qed.
Lemma lem3454977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454978 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term87 _89520 _89534 P t f x) = (term88 _89520 _89534 P t f x).
Proof. exact (MK_COMB (@lem3454977) (@lem3454976 _89520 _89534 P t f x)). Qed.
Lemma lem3454979 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (@IN _89520 x t) = (@IN _89520 x t).
Proof. exact (eq_refl (@IN _89520 x t)). Qed.
Lemma lem3454980 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89534) (x' : _89520) (t : _89520 -> Prop) : (term89 _89520 _89534 P f x x' t) = (term90 _89520 _89534 P f x x' t).
Proof. exact (MK_COMB (@lem3454978 _89520 _89534 P t f x) (@lem3454979 _89520 x' t)). Qed.
Lemma lem3454981 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term91 _89520 _89534 P f x t) = (term92 _89520 _89534 P f x t).
Proof. exact (fun_ext (fun x' : _89534 => @lem3454980 _89520 _89534 P f x' x t)). Qed.
Lemma lem3454982 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3454983 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term81 _89520 _89534 P f x t) = (term93 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3454982 _89534) (@lem3454981 _89520 _89534 P f x t)). Qed.
Lemma lem3454984 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : ((term80 _89520 _89534 P f x t) = (term81 _89520 _89534 P f x t)) = ((term24 _89520 _89534 P f x t) = (term93 _89520 _89534 P f x t)).
Proof. exact (MK_COMB (@lem3454975 _89520 _89534 P f x t) (@lem3454983 _89520 _89534 P f x t)). Qed.
Lemma lem3454985 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term24 _89520 _89534 P f x t) = (term93 _89520 _89534 P f x t).
Proof. exact (EQ_MP (@lem3454984 _89520 _89534 P f x t) (@lem3454965 _89520 _89534 P f x t)). Qed.
Lemma lem3454986 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term25 _89520 _89534 P f x) = (term94 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3454985 _89520 _89534 P f x t)). Qed.
Lemma lem3454987 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3454988 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term26 _89520 _89534 P f x) = (term95 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454987 _89520) (@lem3454986 _89520 _89534 P f x)). Qed.
Lemma lem3454989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454990 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term71 _89520 _89534 P f x) = (term96 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454989) (@lem3454988 _89520 _89534 P f x)). Qed.
Lemma lem3454991 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term66 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (eq_refl (term66 _89520 _89534 P x f)). Qed.
Lemma lem3454992 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term73 _89520 _89534 P x f) = (term97 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3454990 _89520 _89534 P f x) (@lem3454991 _89520 _89534 P x f)). Qed.
Lemma lem3454994 {A : Type'} (P : A -> Prop) (Q : Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3454995 {_89520 : Type'} (P : type686 _89520) (Q : Prop) : (term98 _89520 P Q) = (term99 _89520 P Q).
Proof. exact (@lem3454994 (_89520 -> Prop) P Q). Qed.
Lemma lem3454996 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term100 _89520 _89534 P x f) = (term101 _89520 _89534 P x f).
Proof. exact (@lem3454995 _89520 (term94 _89520 _89534 P f x) (term66 _89520 _89534 P x f)). Qed.
Lemma lem3454997 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term102 _89520 _89534 P f x t) = (term93 _89520 _89534 P f x t).
Proof. exact (eq_refl (term102 _89520 _89534 P f x t)). Qed.
Lemma lem3454998 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term103 _89520 _89534 P f x) = (term94 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3454997 _89520 _89534 P f x t)). Qed.
Lemma lem3454999 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3455000 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term104 _89520 _89534 P f x) = (term95 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3454999 _89520) (@lem3454998 _89520 _89534 P f x)). Qed.
Lemma lem3455001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3455002 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term105 _89520 _89534 P f x) = (term96 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3455001) (@lem3455000 _89520 _89534 P f x)). Qed.
Lemma lem3455003 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term66 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (eq_refl (term66 _89520 _89534 P x f)). Qed.
Lemma lem3455004 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term100 _89520 _89534 P x f) = (term97 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455002 _89520 _89534 P f x) (@lem3455003 _89520 _89534 P x f)). Qed.
Lemma lem3455005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455006 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term106 _89520 _89534 P x f) = (term107 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455005) (@lem3455004 _89520 _89534 P x f)). Qed.
Lemma lem3455007 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term102 _89520 _89534 P f x t) = (term93 _89520 _89534 P f x t).
Proof. exact (eq_refl (term102 _89520 _89534 P f x t)). Qed.
Lemma lem3455008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3455009 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term108 _89520 _89534 P f x t) = (term109 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455008) (@lem3455007 _89520 _89534 P f x t)). Qed.
Lemma lem3455010 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term66 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (eq_refl (term66 _89520 _89534 P x f)). Qed.
Lemma lem3455011 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term110 _89520 _89534 t P x f) = (term111 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455009 _89520 _89534 P f x t) (@lem3455010 _89520 _89534 P x f)). Qed.
Lemma lem3455012 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term112 _89520 _89534 P x f) = (term113 _89520 _89534 P x f).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455011 _89520 _89534 t P x f)). Qed.
Lemma lem3455013 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3455014 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term101 _89520 _89534 P x f) = (term114 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455013 _89520) (@lem3455012 _89520 _89534 P x f)). Qed.
Lemma lem3455015 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term100 _89520 _89534 P x f) = (term101 _89520 _89534 P x f)) = ((term97 _89520 _89534 P x f) = (term114 _89520 _89534 P x f)).
Proof. exact (MK_COMB (@lem3455006 _89520 _89534 P x f) (@lem3455014 _89520 _89534 P x f)). Qed.
Lemma lem3455016 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term97 _89520 _89534 P x f) = (term114 _89520 _89534 P x f).
Proof. exact (EQ_MP (@lem3455015 _89520 _89534 P x f) (@lem3454996 _89520 _89534 P x f)). Qed.
Lemma lem3455018 {A : Type'} (P : A -> Prop) (Q : Prop) : (term78 A P Q) = (term79 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3455019 {_89534 : Type'} (P : _89534 -> Prop) (Q : Prop) : (term78 _89534 P Q) = (term79 _89534 P Q).
Proof. exact (@lem3455018 _89534 P Q). Qed.
Lemma lem3455020 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term115 _89520 _89534 t P x f) = (term116 _89520 _89534 t P x f).
Proof. exact (@lem3455019 _89534 (term92 _89520 _89534 P f x t) (term66 _89520 _89534 P x f)). Qed.
Lemma lem3455021 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89534) (x' : _89520) (t : _89520 -> Prop) : (term117 _89520 _89534 P f x' t x) = (term90 _89520 _89534 P f x x' t).
Proof. exact (eq_refl (term117 _89520 _89534 P f x' t x)). Qed.
Lemma lem3455022 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term118 _89520 _89534 P f x t) = (term92 _89520 _89534 P f x t).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455021 _89520 _89534 P f x' x t)). Qed.
Lemma lem3455023 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3455024 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term119 _89520 _89534 P f x t) = (term93 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455023 _89534) (@lem3455022 _89520 _89534 P f x t)). Qed.
Lemma lem3455025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3455026 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term120 _89520 _89534 P f x t) = (term109 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455025) (@lem3455024 _89520 _89534 P f x t)). Qed.
Lemma lem3455027 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term66 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (eq_refl (term66 _89520 _89534 P x f)). Qed.
Lemma lem3455028 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term115 _89520 _89534 t P x f) = (term111 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455026 _89520 _89534 P f x t) (@lem3455027 _89520 _89534 P x f)). Qed.
Lemma lem3455029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455030 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term121 _89520 _89534 t P x f) = (term122 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455029) (@lem3455028 _89520 _89534 t P x f)). Qed.
Lemma lem3455031 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89534) (x' : _89520) (t : _89520 -> Prop) : (term117 _89520 _89534 P f x' t x) = (term90 _89520 _89534 P f x x' t).
Proof. exact (eq_refl (term117 _89520 _89534 P f x' t x)). Qed.
Lemma lem3455032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3455033 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89534) (x' : _89520) (t : _89520 -> Prop) : (term123 _89520 _89534 P f x' t x) = (term124 _89520 _89534 P f x x' t).
Proof. exact (MK_COMB (@lem3455032) (@lem3455031 _89520 _89534 P f x x' t)). Qed.
Lemma lem3455034 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term66 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (eq_refl (term66 _89520 _89534 P x f)). Qed.
Lemma lem3455035 {_89520 _89534 : Type'} (x : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x' : _89520) (f : type1470 _89520 _89534) : (term125 _89520 _89534 t x P x' f) = (term126 _89520 _89534 x t P x' f).
Proof. exact (MK_COMB (@lem3455033 _89520 _89534 P f x x' t) (@lem3455034 _89520 _89534 P x' f)). Qed.
Lemma lem3455036 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term127 _89520 _89534 t P x f) = (term128 _89520 _89534 t P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455035 _89520 _89534 x' t P x f)). Qed.
Lemma lem3455037 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3455038 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term116 _89520 _89534 t P x f) = (term129 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455037 _89534) (@lem3455036 _89520 _89534 t P x f)). Qed.
Lemma lem3455039 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term115 _89520 _89534 t P x f) = (term116 _89520 _89534 t P x f)) = ((term111 _89520 _89534 t P x f) = (term129 _89520 _89534 t P x f)).
Proof. exact (MK_COMB (@lem3455030 _89520 _89534 t P x f) (@lem3455038 _89520 _89534 t P x f)). Qed.
Lemma lem3455040 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term111 _89520 _89534 t P x f) = (term129 _89520 _89534 t P x f).
Proof. exact (EQ_MP (@lem3455039 _89520 _89534 t P x f) (@lem3455020 _89520 _89534 t P x f)). Qed.
Lemma lem3455041 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term113 _89520 _89534 P x f) = (term130 _89520 _89534 P x f).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455040 _89520 _89534 t P x f)). Qed.
Lemma lem3455042 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3455043 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term114 _89520 _89534 P x f) = (term131 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455042 _89520) (@lem3455041 _89520 _89534 P x f)). Qed.
Lemma lem3455044 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term97 _89520 _89534 P x f) = (term131 _89520 _89534 P x f).
Proof. exact (TRANS (@lem3455016 _89520 _89534 P x f) (@lem3455043 _89520 _89534 P x f)). Qed.
Lemma lem3455045 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term73 _89520 _89534 P x f) = (term131 _89520 _89534 P x f).
Proof. exact (TRANS (@lem3454992 _89520 _89534 P x f) (@lem3455044 _89520 _89534 P x f)). Qed.
Lemma lem3455046 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455047 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term75 _89520 _89534 P x f) = (term132 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455046) (@lem3455045 _89520 _89534 P x f)). Qed.
Lemma lem3455049 {A : Type'} (P : Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3455050 {_89534 : Type'} (P : Prop) (Q : _89534 -> Prop) : (term133 _89534 P Q) = (term134 _89534 P Q).
Proof. exact (@lem3455049 _89534 P Q). Qed.
Lemma lem3455051 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term135 _89520 _89534 P x f) = (term136 _89520 _89534 P x f).
Proof. exact (@lem3455050 _89534 (term56 _89520 _89534 P f x) (term18 _89520 _89534 P x f)). Qed.
Lemma lem3455052 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term62 _89520 _89534 P x f x') = (term17 _89520 _89534 P x f x').
Proof. exact (eq_refl (term62 _89520 _89534 P x f x')). Qed.
Lemma lem3455053 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term137 _89520 _89534 P x f) = (term18 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455052 _89520 _89534 P x f x')). Qed.
Lemma lem3455054 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3455055 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term138 _89520 _89534 P x f) = (term19 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455054 _89534) (@lem3455053 _89520 _89534 P x f)). Qed.
Lemma lem3455056 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term68 _89520 _89534 P f x) = (term68 _89520 _89534 P f x).
Proof. exact (eq_refl (term68 _89520 _89534 P f x)). Qed.
Lemma lem3455057 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term135 _89520 _89534 P x f) = (term70 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455056 _89520 _89534 P f x) (@lem3455055 _89520 _89534 P x f)). Qed.
Lemma lem3455058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455059 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term139 _89520 _89534 P x f) = (term140 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455058) (@lem3455057 _89520 _89534 P x f)). Qed.
Lemma lem3455060 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term62 _89520 _89534 P x f x') = (term17 _89520 _89534 P x f x').
Proof. exact (eq_refl (term62 _89520 _89534 P x f x')). Qed.
Lemma lem3455061 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term68 _89520 _89534 P f x) = (term68 _89520 _89534 P f x).
Proof. exact (eq_refl (term68 _89520 _89534 P f x)). Qed.
Lemma lem3455062 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term141 _89520 _89534 P x f x') = (term142 _89520 _89534 P x f x').
Proof. exact (MK_COMB (@lem3455061 _89520 _89534 P f x) (@lem3455060 _89520 _89534 P x f x')). Qed.
Lemma lem3455063 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term143 _89520 _89534 P x f) = (term144 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455062 _89520 _89534 P x f x')). Qed.
Lemma lem3455064 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3455065 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term136 _89520 _89534 P x f) = (term145 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455064 _89534) (@lem3455063 _89520 _89534 P x f)). Qed.
Lemma lem3455066 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term135 _89520 _89534 P x f) = (term136 _89520 _89534 P x f)) = ((term70 _89520 _89534 P x f) = (term145 _89520 _89534 P x f)).
Proof. exact (MK_COMB (@lem3455059 _89520 _89534 P x f) (@lem3455065 _89520 _89534 P x f)). Qed.
Lemma lem3455067 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term70 _89520 _89534 P x f) = (term145 _89520 _89534 P x f).
Proof. exact (EQ_MP (@lem3455066 _89520 _89534 P x f) (@lem3455051 _89520 _89534 P x f)). Qed.
Lemma lem3455068 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term77 _89520 _89534 P x f) = (term146 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455047 _89520 _89534 P x f) (@lem3455067 _89520 _89534 P x f)). Qed.
Lemma lem3455072 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3455073 {_89520 : Type'} (P : type686 _89520) (Q : Prop) : (term149 _89520 P Q) = (term150 _89520 P Q).
Proof. exact (@lem3455072 (_89520 -> Prop) P Q). Qed.
Lemma lem3455074 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term151 _89520 _89534 P x f) = (term152 _89520 _89534 P x f).
Proof. exact (@lem3455073 _89520 (term130 _89520 _89534 P x f) (term145 _89520 _89534 P x f)). Qed.
Lemma lem3455075 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term153 _89520 _89534 P x f t) = (term129 _89520 _89534 t P x f).
Proof. exact (eq_refl (term153 _89520 _89534 P x f t)). Qed.
Lemma lem3455076 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term154 _89520 _89534 P x f) = (term130 _89520 _89534 P x f).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455075 _89520 _89534 t P x f)). Qed.
Lemma lem3455077 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3455078 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term155 _89520 _89534 P x f) = (term131 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455077 _89520) (@lem3455076 _89520 _89534 P x f)). Qed.
Lemma lem3455079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455080 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term156 _89520 _89534 P x f) = (term132 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455079) (@lem3455078 _89520 _89534 P x f)). Qed.
Lemma lem3455081 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term145 _89520 _89534 P x f) = (term145 _89520 _89534 P x f).
Proof. exact (eq_refl (term145 _89520 _89534 P x f)). Qed.
Lemma lem3455082 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term151 _89520 _89534 P x f) = (term146 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455080 _89520 _89534 P x f) (@lem3455081 _89520 _89534 P x f)). Qed.
Lemma lem3455083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455084 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term157 _89520 _89534 P x f) = (term158 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455083) (@lem3455082 _89520 _89534 P x f)). Qed.
Lemma lem3455085 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term153 _89520 _89534 P x f t) = (term129 _89520 _89534 t P x f).
Proof. exact (eq_refl (term153 _89520 _89534 P x f t)). Qed.
Lemma lem3455086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455087 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term159 _89520 _89534 P x f t) = (term160 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455086) (@lem3455085 _89520 _89534 t P x f)). Qed.
Lemma lem3455088 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term145 _89520 _89534 P x f) = (term145 _89520 _89534 P x f).
Proof. exact (eq_refl (term145 _89520 _89534 P x f)). Qed.
Lemma lem3455089 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term161 _89520 _89534 t P x f) = (term162 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455087 _89520 _89534 t P x f) (@lem3455088 _89520 _89534 P x f)). Qed.
Lemma lem3455090 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term163 _89520 _89534 P x f) = (term164 _89520 _89534 P x f).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455089 _89520 _89534 t P x f)). Qed.
Lemma lem3455091 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3455092 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term152 _89520 _89534 P x f) = (term165 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455091 _89520) (@lem3455090 _89520 _89534 P x f)). Qed.
Lemma lem3455093 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term151 _89520 _89534 P x f) = (term152 _89520 _89534 P x f)) = ((term146 _89520 _89534 P x f) = (term165 _89520 _89534 P x f)).
Proof. exact (MK_COMB (@lem3455084 _89520 _89534 P x f) (@lem3455092 _89520 _89534 P x f)). Qed.
Lemma lem3455094 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term146 _89520 _89534 P x f) = (term165 _89520 _89534 P x f).
Proof. exact (EQ_MP (@lem3455093 _89520 _89534 P x f) (@lem3455074 _89520 _89534 P x f)). Qed.
Lemma lem3455096 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3455097 {_89534 : Type'} (P : _89534 -> Prop) (Q : _89534 -> Prop) : (term166 _89534 P Q) = (term167 _89534 P Q).
Proof. exact (@lem3455096 _89534 P Q). Qed.
Lemma lem3455098 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term168 _89520 _89534 t P x f) = (term169 _89520 _89534 t P x f).
Proof. exact (@lem3455097 _89534 (term128 _89520 _89534 t P x f) (term144 _89520 _89534 P x f)). Qed.
Lemma lem3455099 {_89520 _89534 : Type'} (x : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x' : _89520) (f : type1470 _89520 _89534) : (term170 _89520 _89534 t P x' f x) = (term126 _89520 _89534 x t P x' f).
Proof. exact (eq_refl (term170 _89520 _89534 t P x' f x)). Qed.
Lemma lem3455100 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term171 _89520 _89534 t P x f) = (term128 _89520 _89534 t P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455099 _89520 _89534 x' t P x f)). Qed.
Lemma lem3455101 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3455102 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term172 _89520 _89534 t P x f) = (term129 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455101 _89534) (@lem3455100 _89520 _89534 t P x f)). Qed.
Lemma lem3455103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455104 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term173 _89520 _89534 t P x f) = (term160 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455103) (@lem3455102 _89520 _89534 t P x f)). Qed.
Lemma lem3455105 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term174 _89520 _89534 P x f x') = (term142 _89520 _89534 P x f x').
Proof. exact (eq_refl (term174 _89520 _89534 P x f x')). Qed.
Lemma lem3455106 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term175 _89520 _89534 P x f) = (term144 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455105 _89520 _89534 P x f x')). Qed.
Lemma lem3455107 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3455108 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term176 _89520 _89534 P x f) = (term145 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455107 _89534) (@lem3455106 _89520 _89534 P x f)). Qed.
Lemma lem3455109 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term168 _89520 _89534 t P x f) = (term162 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455104 _89520 _89534 t P x f) (@lem3455108 _89520 _89534 P x f)). Qed.
Lemma lem3455110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455111 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term177 _89520 _89534 t P x f) = (term178 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455110) (@lem3455109 _89520 _89534 t P x f)). Qed.
Lemma lem3455112 {_89520 _89534 : Type'} (x : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x' : _89520) (f : type1470 _89520 _89534) : (term170 _89520 _89534 t P x' f x) = (term126 _89520 _89534 x t P x' f).
Proof. exact (eq_refl (term170 _89520 _89534 t P x' f x)). Qed.
Lemma lem3455113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455114 {_89520 _89534 : Type'} (x : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x' : _89520) (f : type1470 _89520 _89534) : (term179 _89520 _89534 t P x' f x) = (term180 _89520 _89534 x t P x' f).
Proof. exact (MK_COMB (@lem3455113) (@lem3455112 _89520 _89534 x t P x' f)). Qed.
Lemma lem3455115 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term174 _89520 _89534 P x f x') = (term142 _89520 _89534 P x f x').
Proof. exact (eq_refl (term174 _89520 _89534 P x f x')). Qed.
Lemma lem3455116 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term181 _89520 _89534 t P x f x') = (term182 _89520 _89534 t P x f x').
Proof. exact (MK_COMB (@lem3455114 _89520 _89534 x' t P x f) (@lem3455115 _89520 _89534 P x f x')). Qed.
Lemma lem3455117 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term183 _89520 _89534 t P x f) = (term184 _89520 _89534 t P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455116 _89520 _89534 t P x f x')). Qed.
Lemma lem3455118 {_89534 : Type'} : (@ex _89534) = (@ex _89534).
Proof. exact (eq_refl (@ex _89534)). Qed.
Lemma lem3455119 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term169 _89520 _89534 t P x f) = (term185 _89520 _89534 t P x f).
Proof. exact (MK_COMB (@lem3455118 _89534) (@lem3455117 _89520 _89534 t P x f)). Qed.
Lemma lem3455120 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : ((term168 _89520 _89534 t P x f) = (term169 _89520 _89534 t P x f)) = ((term162 _89520 _89534 t P x f) = (term185 _89520 _89534 t P x f)).
Proof. exact (MK_COMB (@lem3455111 _89520 _89534 t P x f) (@lem3455119 _89520 _89534 t P x f)). Qed.
Lemma lem3455121 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term162 _89520 _89534 t P x f) = (term185 _89520 _89534 t P x f).
Proof. exact (EQ_MP (@lem3455120 _89520 _89534 t P x f) (@lem3455098 _89520 _89534 t P x f)). Qed.
Lemma lem3455122 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term164 _89520 _89534 P x f) = (term186 _89520 _89534 P x f).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455121 _89520 _89534 t P x f)). Qed.
Lemma lem3455123 {_89520 : Type'} : (@ex (_89520 -> Prop)) = (@ex (_89520 -> Prop)).
Proof. exact (eq_refl (@ex (_89520 -> Prop))). Qed.
Lemma lem3455124 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term165 _89520 _89534 P x f) = (term187 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455123 _89520) (@lem3455122 _89520 _89534 P x f)). Qed.
Lemma lem3455125 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term146 _89520 _89534 P x f) = (term187 _89520 _89534 P x f).
Proof. exact (TRANS (@lem3455094 _89520 _89534 P x f) (@lem3455124 _89520 _89534 P x f)). Qed.
Lemma lem3455127 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term77 _89520 _89534 P x f) = (term187 _89520 _89534 P x f).
Proof. exact (TRANS (@lem3455068 _89520 _89534 P x f) (@lem3455125 _89520 _89534 P x f)). Qed.
Lemma lem3455128 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term30 _89520 _89534 P x f) = (term187 _89520 _89534 P x f).
Proof. exact (TRANS (@lem3454712 _89520 _89534 P x f) (@lem3455127 _89520 _89534 P x f)). Qed.
Lemma lem3455129 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term30 _89520 _89534 P x f) : term187 _89520 _89534 P x f.
Proof. exact (EQ_MP (@lem3455128 _89520 _89534 P x f) (@lem3454628 _89520 _89534 P x f h1)). Qed.
Lemma lem3455130 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term185 _89520 _89534 t P x f) : term185 _89520 _89534 t P x f.
Proof. exact (h1). Qed.
Lemma lem3455131 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term182 _89520 _89534 t P x f x') : term182 _89520 _89534 t P x f x'.
Proof. exact (h1). Qed.
Lemma lem3455144 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term17 _89520 _89534 P x f x') = (term17 _89520 _89534 P x f x').
Proof. exact (eq_refl (term17 _89520 _89534 P x f x')). Qed.
Lemma lem3455151 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (term42 _89520 x t) = (term42 _89520 x t).
Proof. exact (eq_refl (term42 _89520 x t)). Qed.
Lemma lem3455168 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term32 _89520 _89534 P t f x) = (term32 _89520 _89534 P t f x).
Proof. exact (eq_refl (term32 _89520 _89534 P t f x)). Qed.
Lemma lem3455169 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term40 _89520 _89534 P t f) = (term40 _89520 _89534 P t f).
Proof. exact (fun_ext (fun x : _89534 => @lem3455168 _89520 _89534 P t f x)). Qed.
Lemma lem3455170 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3455171 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term41 _89520 _89534 P t f) = (term41 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3455170 _89534) (@lem3455169 _89520 _89534 P t f)). Qed.
Lemma lem3455172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455173 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term44 _89520 _89534 P t f) = (term44 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3455172) (@lem3455171 _89520 _89534 P t f)). Qed.
Lemma lem3455174 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term46 _89520 _89534 P f x t) = (term46 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455173 _89520 _89534 P t f) (@lem3455151 _89520 x t)). Qed.
Lemma lem3455175 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term55 _89520 _89534 P f x) = (term55 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455174 _89520 _89534 P f x t)). Qed.
Lemma lem3455176 {_89520 : Type'} : (@all (_89520 -> Prop)) = (@all (_89520 -> Prop)).
Proof. exact (eq_refl (@all (_89520 -> Prop))). Qed.
Lemma lem3455177 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term56 _89520 _89534 P f x) = (term56 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3455176 _89520) (@lem3455175 _89520 _89534 P f x)). Qed.
Lemma lem3455178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3455179 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term68 _89520 _89534 P f x) = (term68 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3455178) (@lem3455177 _89520 _89534 P f x)). Qed.
Lemma lem3455180 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term142 _89520 _89534 P x f x') = (term142 _89520 _89534 P x f x').
Proof. exact (MK_COMB (@lem3455179 _89520 _89534 P f x) (@lem3455144 _89520 _89534 P x f x')). Qed.
Lemma lem3455197 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term58 _89520 _89534 P x f x') = (term58 _89520 _89534 P x f x').
Proof. exact (eq_refl (term58 _89520 _89534 P x f x')). Qed.
Lemma lem3455198 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term65 _89520 _89534 P x f) = (term65 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455197 _89520 _89534 P x f x')). Qed.
Lemma lem3455199 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3455200 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term66 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455199 _89534) (@lem3455198 _89520 _89534 P x f)). Qed.
Lemma lem3455223 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x' : _89534) (x : _89520) (t : _89520 -> Prop) : (term124 _89520 _89534 P f x' x t) = (term124 _89520 _89534 P f x' x t).
Proof. exact (eq_refl (term124 _89520 _89534 P f x' x t)). Qed.
Lemma lem3455224 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term126 _89520 _89534 x' t P x f) = (term126 _89520 _89534 x' t P x f).
Proof. exact (MK_COMB (@lem3455223 _89520 _89534 P f x' x t) (@lem3455200 _89520 _89534 P x f)). Qed.
Lemma lem3455225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455226 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term180 _89520 _89534 x' t P x f) = (term180 _89520 _89534 x' t P x f).
Proof. exact (MK_COMB (@lem3455225) (@lem3455224 _89520 _89534 x' t P x f)). Qed.
Lemma lem3455227 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term182 _89520 _89534 t P x f x') = (term182 _89520 _89534 t P x f x').
Proof. exact (MK_COMB (@lem3455226 _89520 _89534 x' t P x f) (@lem3455180 _89520 _89534 P x f x')). Qed.
Lemma lem3455228 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term182 _89520 _89534 t P x f x') : term182 _89520 _89534 t P x f x'.
Proof. exact (EQ_MP (@lem3455227 _89520 _89534 t P x f x') (@lem3455131 _89520 _89534 t P x f x' h1)). Qed.
Lemma lem3455229 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term126 _89520 _89534 x' t P x f.
Proof. exact (h1). Qed.
Lemma lem3455230 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term142 _89520 _89534 P x f x'.
Proof. exact (h1). Qed.
Lemma lem3455231 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term66 _89520 _89534 P x f.
Proof. exact (proj2 (@lem3455229 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455232 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term90 _89520 _89534 P f x' x t.
Proof. exact (proj1 (@lem3455229 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455234 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term20 _89520 _89534 P t f x'.
Proof. exact (proj1 (@lem3455232 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455237 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term17 _89520 _89534 P x f x'.
Proof. exact (proj2 (@lem3455230 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455238 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term56 _89520 _89534 P f x.
Proof. exact (proj1 (@lem3455230 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455248 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term58 _89520 _89534 P x f x') = (term58 _89520 _89534 P x f x').
Proof. exact (eq_refl (term58 _89520 _89534 P x f x')). Qed.
Lemma lem3455249 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term65 _89520 _89534 P x f) = (term65 _89520 _89534 P x f).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455248 _89520 _89534 P x f x')). Qed.
Lemma lem3455250 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3455252 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term66 _89520 _89534 P x f) = (term66 _89520 _89534 P x f).
Proof. exact (MK_COMB (@lem3455250 _89534) (@lem3455249 _89520 _89534 P x f)). Qed.
Lemma lem3455253 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term66 _89520 _89534 P x f.
Proof. exact (EQ_MP (@lem3455252 _89520 _89534 P x f) (@lem3455231 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455267 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3455268 {_89534 : Type'} (P : _89534 -> Prop) (Q : Prop) : (term188 _89534 P Q) = (term189 _89534 P Q).
Proof. exact (@lem3455267 _89534 P Q). Qed.
Lemma lem3455269 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term190 _89520 _89534 P f x t) = (term191 _89520 _89534 P f x t).
Proof. exact (@lem3455268 _89534 (term40 _89520 _89534 P t f) (term42 _89520 x t)). Qed.
Lemma lem3455270 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term192 _89520 _89534 P t f x) = (term32 _89520 _89534 P t f x).
Proof. exact (eq_refl (term192 _89520 _89534 P t f x)). Qed.
Lemma lem3455271 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term193 _89520 _89534 P t f) = (term40 _89520 _89534 P t f).
Proof. exact (fun_ext (fun x : _89534 => @lem3455270 _89520 _89534 P t f x)). Qed.
Lemma lem3455272 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3455273 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term194 _89520 _89534 P t f) = (term41 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3455272 _89534) (@lem3455271 _89520 _89534 P t f)). Qed.
Lemma lem3455274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455275 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) : (term195 _89520 _89534 P t f) = (term44 _89520 _89534 P t f).
Proof. exact (MK_COMB (@lem3455274) (@lem3455273 _89520 _89534 P t f)). Qed.
Lemma lem3455276 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (term42 _89520 x t) = (term42 _89520 x t).
Proof. exact (eq_refl (term42 _89520 x t)). Qed.
Lemma lem3455277 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term190 _89520 _89534 P f x t) = (term46 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455275 _89520 _89534 P t f) (@lem3455276 _89520 x t)). Qed.
Lemma lem3455278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455279 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term196 _89520 _89534 P f x t) = (term197 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455278) (@lem3455277 _89520 _89534 P f x t)). Qed.
Lemma lem3455280 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term192 _89520 _89534 P t f x) = (term32 _89520 _89534 P t f x).
Proof. exact (eq_refl (term192 _89520 _89534 P t f x)). Qed.
Lemma lem3455281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455282 {_89520 _89534 : Type'} (P : _89534 -> Prop) (t : _89520 -> Prop) (f : type1470 _89520 _89534) (x : _89534) : (term198 _89520 _89534 P t f x) = (term199 _89520 _89534 P t f x).
Proof. exact (MK_COMB (@lem3455281) (@lem3455280 _89520 _89534 P t f x)). Qed.
Lemma lem3455283 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (term42 _89520 x t) = (term42 _89520 x t).
Proof. exact (eq_refl (term42 _89520 x t)). Qed.
Lemma lem3455284 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89534) (x' : _89520) (t : _89520 -> Prop) : (term200 _89520 _89534 P f x x' t) = (term201 _89520 _89534 P f x x' t).
Proof. exact (MK_COMB (@lem3455282 _89520 _89534 P t f x) (@lem3455283 _89520 x' t)). Qed.
Lemma lem3455285 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term202 _89520 _89534 P f x t) = (term203 _89520 _89534 P f x t).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455284 _89520 _89534 P f x' x t)). Qed.
Lemma lem3455286 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3455287 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term191 _89520 _89534 P f x t) = (term204 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455286 _89534) (@lem3455285 _89520 _89534 P f x t)). Qed.
Lemma lem3455288 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : ((term190 _89520 _89534 P f x t) = (term191 _89520 _89534 P f x t)) = ((term46 _89520 _89534 P f x t) = (term204 _89520 _89534 P f x t)).
Proof. exact (MK_COMB (@lem3455279 _89520 _89534 P f x t) (@lem3455287 _89520 _89534 P f x t)). Qed.
Lemma lem3455289 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term46 _89520 _89534 P f x t) = (term204 _89520 _89534 P f x t).
Proof. exact (EQ_MP (@lem3455288 _89520 _89534 P f x t) (@lem3455269 _89520 _89534 P f x t)). Qed.
Lemma lem3455290 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term55 _89520 _89534 P f x) = (term205 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455289 _89520 _89534 P f x t)). Qed.
Lemma lem3455291 {_89520 : Type'} : (@all (_89520 -> Prop)) = (@all (_89520 -> Prop)).
Proof. exact (eq_refl (@all (_89520 -> Prop))). Qed.
Lemma lem3455292 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term56 _89520 _89534 P f x) = (term206 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3455291 _89520) (@lem3455290 _89520 _89534 P f x)). Qed.
Lemma lem3455305 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89534) (x' : _89520) (t : _89520 -> Prop) : (term201 _89520 _89534 P f x x' t) = (term201 _89520 _89534 P f x x' t).
Proof. exact (eq_refl (term201 _89520 _89534 P f x x' t)). Qed.
Lemma lem3455306 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term203 _89520 _89534 P f x t) = (term203 _89520 _89534 P f x t).
Proof. exact (fun_ext (fun x' : _89534 => @lem3455305 _89520 _89534 P f x' x t)). Qed.
Lemma lem3455307 {_89534 : Type'} : (@all _89534) = (@all _89534).
Proof. exact (eq_refl (@all _89534)). Qed.
Lemma lem3455308 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (t : _89520 -> Prop) : (term204 _89520 _89534 P f x t) = (term204 _89520 _89534 P f x t).
Proof. exact (MK_COMB (@lem3455307 _89534) (@lem3455306 _89520 _89534 P f x t)). Qed.
Lemma lem3455309 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term205 _89520 _89534 P f x) = (term205 _89520 _89534 P f x).
Proof. exact (fun_ext (fun t : _89520 -> Prop => @lem3455308 _89520 _89534 P f x t)). Qed.
Lemma lem3455310 {_89520 : Type'} : (@all (_89520 -> Prop)) = (@all (_89520 -> Prop)).
Proof. exact (eq_refl (@all (_89520 -> Prop))). Qed.
Lemma lem3455311 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term206 _89520 _89534 P f x) = (term206 _89520 _89534 P f x).
Proof. exact (MK_COMB (@lem3455310 _89520) (@lem3455309 _89520 _89534 P f x)). Qed.
Lemma lem3455312 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) : (term56 _89520 _89534 P f x) = (term206 _89520 _89534 P f x).
Proof. exact (TRANS (@lem3455292 _89520 _89534 P f x) (@lem3455311 _89520 _89534 P f x)). Qed.
Lemma lem3455313 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term206 _89520 _89534 P f x.
Proof. exact (EQ_MP (@lem3455312 _89520 _89534 P f x) (@lem3455238 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455322 {_89520 _89534 : Type'} (_36439 : _89534) (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term207 _89520 _89534 P x f _36439.
Proof. exact (@lem3455253 _89520 _89534 x' t P x f h1 _36439). Qed.
Lemma lem3455323 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (_36439 : _89534) : (term207 _89520 _89534 P x f _36439) = (term58 _89520 _89534 P x f _36439).
Proof. exact (eq_refl (term207 _89520 _89534 P x f _36439)). Qed.
Lemma lem3455325 {_89520 _89534 : Type'} (_36440 : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term208 _89520 _89534 P f x _36440.
Proof. exact (@lem3455313 _89520 _89534 P x f x' h1 _36440). Qed.
Lemma lem3455326 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term208 _89520 _89534 P f x _36440) = (term204 _89520 _89534 P f x _36440).
Proof. exact (eq_refl (term208 _89520 _89534 P f x _36440)). Qed.
Lemma lem3455327 {_89520 _89534 : Type'} (_36440 : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term204 _89520 _89534 P f x _36440.
Proof. exact (EQ_MP (@lem3455326 _89520 _89534 P f x _36440) (@lem3455325 _89520 _89534 _36440 P x f x' h1)). Qed.
Lemma lem3455328 {_89520 _89534 : Type'} (_36440 : _89520 -> Prop) (_36441 : _89534) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term209 _89520 _89534 P f x _36440 _36441.
Proof. exact (@lem3455327 _89520 _89534 _36440 P x f x' h1 _36441). Qed.
Lemma lem3455329 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term209 _89520 _89534 P f x _36440 _36441) = (term201 _89520 _89534 P f _36441 x _36440).
Proof. exact (eq_refl (term209 _89520 _89534 P f x _36440 _36441)). Qed.
Lemma lem3455330 {_89520 _89534 : Type'} (_36441 : _89534) (_36440 : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term201 _89520 _89534 P f _36441 x _36440.
Proof. exact (EQ_MP (@lem3455329 _89520 _89534 P f _36441 x _36440) (@lem3455328 _89520 _89534 _36440 _36441 P x f x' h1)). Qed.
Lemma lem3455338 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : @IN _89520 x t.
Proof. exact (proj2 (@lem3455232 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455342 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : t = (f x').
Proof. exact (proj2 (@lem3455234 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455353 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term201 _89520 _89534 P f _36441 x _36440) = (term210 _89520 _89534 P f _36441 x _36440).
Proof. exact (@lem3453857 (term211 _89534 P _36441) (term212 _89520 _89534 _36440 f _36441) (term42 _89520 x _36440)). Qed.
Lemma lem3455354 {_89520 _89534 : Type'} (_36441 : _89534) (_36440 : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term210 _89520 _89534 P f _36441 x _36440.
Proof. exact (EQ_MP (@lem3455353 _89520 _89534 P f _36441 x _36440) (@lem3455330 _89520 _89534 _36441 _36440 P x f x' h1)). Qed.
Lemma lem3455386 {_89520 _89534 : Type'} (_36439 : _89534) (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term58 _89520 _89534 P x f _36439.
Proof. exact (EQ_MP (@lem3455323 _89520 _89534 P x f _36439) (@lem3455322 _89520 _89534 _36439 x' t P x f h1)). Qed.
Lemma lem3455387 {_89520 : Type'} (x : _89520) : (term213 _89520 x) = (term213 _89520 x).
Proof. exact (eq_refl (term213 _89520 x)). Qed.
Lemma lem3455388 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : (term214 _89520 x t) = (term215 _89520 _89534 x f x').
Proof. exact (MK_COMB (@lem3455387 _89520 x) (@lem3455342 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455389 {_89520 _89534 : Type'} (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term215 _89520 _89534 x f x') = (term59 _89520 _89534 x f x').
Proof. exact (eq_refl (term215 _89520 _89534 x f x')). Qed.
Lemma lem3455390 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (term216 _89520 x t) = (term216 _89520 x t).
Proof. exact (eq_refl (term216 _89520 x t)). Qed.
Lemma lem3455391 {_89520 _89534 : Type'} (t : _89520 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : ((term214 _89520 x t) = (term215 _89520 _89534 x f x')) = ((term214 _89520 x t) = (term59 _89520 _89534 x f x')).
Proof. exact (MK_COMB (@lem3455390 _89520 x t) (@lem3455389 _89520 _89534 x f x')). Qed.
Lemma lem3455392 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (term214 _89520 x t) = (@IN _89520 x t).
Proof. exact (eq_refl (term214 _89520 x t)). Qed.
Lemma lem3455393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455394 {_89520 : Type'} (x : _89520) (t : _89520 -> Prop) : (term216 _89520 x t) = (term217 _89520 x t).
Proof. exact (MK_COMB (@lem3455393) (@lem3455392 _89520 x t)). Qed.
Lemma lem3455395 {_89520 _89534 : Type'} (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term59 _89520 _89534 x f x') = (term59 _89520 _89534 x f x').
Proof. exact (eq_refl (term59 _89520 _89534 x f x')). Qed.
Lemma lem3455396 {_89520 _89534 : Type'} (t : _89520 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : ((term214 _89520 x t) = (term59 _89520 _89534 x f x')) = ((@IN _89520 x t) = (term59 _89520 _89534 x f x')).
Proof. exact (MK_COMB (@lem3455394 _89520 x t) (@lem3455395 _89520 _89534 x f x')). Qed.
Lemma lem3455397 {_89520 _89534 : Type'} (t : _89520 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : ((term214 _89520 x t) = (term215 _89520 _89534 x f x')) = ((@IN _89520 x t) = (term59 _89520 _89534 x f x')).
Proof. exact (TRANS (@lem3455391 _89520 _89534 t x f x') (@lem3455396 _89520 _89534 t x f x')). Qed.
Lemma lem3455398 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : (@IN _89520 x t) = (term59 _89520 _89534 x f x').
Proof. exact (EQ_MP (@lem3455397 _89520 _89534 t x f x') (@lem3455388 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455415 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : P x'.
Proof. exact (proj1 (@lem3455234 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455416 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term218 _89534 P x'.
Proof. exact (fun h0 : term211 _89534 P x' => @lem3455415 _89520 _89534 x' t P x f h1). Qed.
Lemma lem3455418 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3455419 {_89534 : Type'} (P : _89534 -> Prop) (x' : _89534) : (term218 _89534 P x') = (P x').
Proof. exact (@lem3455418 (P x')). Qed.
Lemma lem3455420 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : P x'.
Proof. exact (EQ_MP (@lem3455419 _89534 P x') (@lem3455416 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455422 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term59 _89520 _89534 x f x'.
Proof. exact (EQ_MP (@lem3455398 _89520 _89534 x' t P x f h1) (@lem3455338 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455423 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term220 _89520 _89534 x f x'.
Proof. exact (fun h0 : term221 _89520 _89534 x f x' => @lem3455422 _89520 _89534 x' t P x f h1). Qed.
Lemma lem3455425 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3455426 {_89520 _89534 : Type'} (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term220 _89520 _89534 x f x') = (term59 _89520 _89534 x f x').
Proof. exact (@lem3455425 (term59 _89520 _89534 x f x')). Qed.
Lemma lem3455427 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term59 _89520 _89534 x f x'.
Proof. exact (EQ_MP (@lem3455426 _89520 _89534 x f x') (@lem3455423 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455429 (a : Prop) (b : Prop) : (term222 a b) = (term223 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3455430 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (_36439 : _89534) : (term58 _89520 _89534 P x f _36439) = (term57 _89520 _89534 P x f _36439).
Proof. exact (@lem3455429 (P _36439) (term59 _89520 _89534 x f _36439)). Qed.
Lemma lem3455432 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3455433 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (_36439 : _89534) : (term57 _89520 _89534 P x f _36439) = (term224 _89520 _89534 P x f _36439).
Proof. exact (@lem3455432 (term17 _89520 _89534 P x f _36439)). Qed.
Lemma lem3455434 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (_36439 : _89534) : (term58 _89520 _89534 P x f _36439) = (term224 _89520 _89534 P x f _36439).
Proof. exact (TRANS (@lem3455430 _89520 _89534 P x f _36439) (@lem3455433 _89520 _89534 P x f _36439)). Qed.
Lemma lem3455436 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term17 _89520 _89534 P x f x'.
Proof. exact (conj (@lem3455420 _89520 _89534 x' t P x f h1) (@lem3455427 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455438 {_89520 _89534 : Type'} (_36439 : _89534) (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term224 _89520 _89534 P x f _36439.
Proof. exact (EQ_MP (@lem3455434 _89520 _89534 P x f _36439) (@lem3455386 _89520 _89534 _36439 x' t P x f h1)). Qed.
Lemma lem3455439 {_89520 _89534 : Type'} (_36439 : _89534) (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term224 _89520 _89534 P x f _36439.
Proof. exact (@lem3455438 _89520 _89534 _36439 x' t P x f h1). Qed.
Lemma lem3455440 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term224 _89520 _89534 P x f x'.
Proof. exact (@lem3455439 _89520 _89534 x' x' t P x f h1). Qed.
Lemma lem3455443 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : False.
Proof. exact (@lem3455440 _89520 _89534 x' t P x f h1 (@lem3455436 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455444 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : term225.
Proof. exact (fun h0 : ~ False => @lem3455443 _89520 _89534 x' t P x f h1). Qed.
Lemma lem3455446 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3455447 : term225 = False.
Proof. exact (@lem3455446 False). Qed.
Lemma lem3455495 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : P x'.
Proof. exact (proj1 (@lem3455237 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455496 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term218 _89534 P x'.
Proof. exact (fun h0 : term211 _89534 P x' => @lem3455495 _89520 _89534 P x f x' h1). Qed.
Lemma lem3455498 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3455499 {_89534 : Type'} (P : _89534 -> Prop) (x' : _89534) : (term218 _89534 P x') = (P x').
Proof. exact (@lem3455498 (P x')). Qed.
Lemma lem3455500 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : P x'.
Proof. exact (EQ_MP (@lem3455499 _89534 P x') (@lem3455496 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455502 {_89520 : Type'} (x : _89520 -> Prop) : x = x.
Proof. exact (@lem21386 (_89520 -> Prop) x). Qed.
Lemma lem3455503 {_89520 : Type'} (x : _89520 -> Prop) : x = x.
Proof. exact (@lem3455502 _89520 x). Qed.
Lemma lem3455504 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (x' : _89534) : (f x') = (f x').
Proof. exact (@lem3455503 _89520 (f x')). Qed.
Lemma lem3455505 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (x' : _89534) : term226 _89520 _89534 f x'.
Proof. exact (fun h0 : term227 _89520 _89534 f x' => @lem3455504 _89520 _89534 f x'). Qed.
Lemma lem3455507 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3455508 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (x' : _89534) : (term226 _89520 _89534 f x') = ((f x') = (f x')).
Proof. exact (@lem3455507 ((f x') = (f x'))). Qed.
Lemma lem3455509 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (x' : _89534) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3455508 _89520 _89534 f x') (@lem3455505 _89520 _89534 f x')). Qed.
Lemma lem3455511 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term59 _89520 _89534 x f x'.
Proof. exact (proj2 (@lem3455237 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455512 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term220 _89520 _89534 x f x'.
Proof. exact (fun h0 : term221 _89520 _89534 x f x' => @lem3455511 _89520 _89534 P x f x' h1). Qed.
Lemma lem3455514 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3455515 {_89520 _89534 : Type'} (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) : (term220 _89520 _89534 x f x') = (term59 _89520 _89534 x f x').
Proof. exact (@lem3455514 (term59 _89520 _89534 x f x')). Qed.
Lemma lem3455516 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term59 _89520 _89534 x f x'.
Proof. exact (EQ_MP (@lem3455515 _89520 _89534 x f x') (@lem3455512 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455518 (a : Prop) (b : Prop) : (term222 a b) = (term223 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3455519 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term228 _89520 _89534 f _36441 x _36440) = (term229 _89520 _89534 f _36441 x _36440).
Proof. exact (@lem3455518 (_36440 = (f _36441)) (@IN _89520 x _36440)). Qed.
Lemma lem3455520 {_89534 : Type'} (P : _89534 -> Prop) (_36441 : _89534) : (term230 _89534 P _36441) = (term230 _89534 P _36441).
Proof. exact (eq_refl (term230 _89534 P _36441)). Qed.
Lemma lem3455521 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term210 _89520 _89534 P f _36441 x _36440) = (term231 _89520 _89534 P f _36441 x _36440).
Proof. exact (MK_COMB (@lem3455520 _89534 P _36441) (@lem3455519 _89520 _89534 f _36441 x _36440)). Qed.
Lemma lem3455523 (a : Prop) (b : Prop) : (term222 a b) = (term223 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3455524 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term231 _89520 _89534 P f _36441 x _36440) = (term232 _89520 _89534 P f _36441 x _36440).
Proof. exact (@lem3455523 (P _36441) (term233 _89520 _89534 f _36441 x _36440)). Qed.
Lemma lem3455525 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term210 _89520 _89534 P f _36441 x _36440) = (term232 _89520 _89534 P f _36441 x _36440).
Proof. exact (TRANS (@lem3455521 _89520 _89534 P f _36441 x _36440) (@lem3455524 _89520 _89534 P f _36441 x _36440)). Qed.
Lemma lem3455527 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3455528 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term232 _89520 _89534 P f _36441 x _36440) = (term234 _89520 _89534 P f _36441 x _36440).
Proof. exact (@lem3455527 (term235 _89520 _89534 P f _36441 x _36440)). Qed.
Lemma lem3455529 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (_36441 : _89534) (x : _89520) (_36440 : _89520 -> Prop) : (term210 _89520 _89534 P f _36441 x _36440) = (term234 _89520 _89534 P f _36441 x _36440).
Proof. exact (TRANS (@lem3455525 _89520 _89534 P f _36441 x _36440) (@lem3455528 _89520 _89534 P f _36441 x _36440)). Qed.
Lemma lem3455531 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term236 _89520 _89534 x f x'.
Proof. exact (conj (@lem3455509 _89520 _89534 f x') (@lem3455516 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455532 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term237 _89520 _89534 P x f x'.
Proof. exact (conj (@lem3455500 _89520 _89534 P x f x' h1) (@lem3455531 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455534 {_89520 _89534 : Type'} (_36441 : _89534) (_36440 : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term234 _89520 _89534 P f _36441 x _36440.
Proof. exact (EQ_MP (@lem3455529 _89520 _89534 P f _36441 x _36440) (@lem3455354 _89520 _89534 _36441 _36440 P x f x' h1)). Qed.
Lemma lem3455535 {_89520 _89534 : Type'} (_36441 : _89534) (_36440 : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term234 _89520 _89534 P f _36441 x _36440.
Proof. exact (@lem3455534 _89520 _89534 _36441 _36440 P x f x' h1). Qed.
Lemma lem3455536 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term238 _89520 _89534 P x f x'.
Proof. exact (@lem3455535 _89520 _89534 x' (f x') P x f x' h1). Qed.
Lemma lem3455539 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : False.
Proof. exact (@lem3455536 _89520 _89534 P x f x' h1 (@lem3455532 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455540 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : term225.
Proof. exact (fun h0 : ~ False => @lem3455539 _89520 _89534 P x f x' h1). Qed.
Lemma lem3455542 (p : Prop) : (term219 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3455543 : term225 = False.
Proof. exact (@lem3455542 False). Qed.
Lemma lem3455544 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term142 _89520 _89534 P x f x') : False.
Proof. exact (EQ_MP (@lem3455543) (@lem3455540 _89520 _89534 P x f x' h1)). Qed.
Lemma lem3455545 {_89520 _89534 : Type'} (x' : _89534) (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term126 _89520 _89534 x' t P x f) : False.
Proof. exact (EQ_MP (@lem3455447) (@lem3455444 _89520 _89534 x' t P x f h1)). Qed.
Lemma lem3455546 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term182 _89520 _89534 t P x f x') : False.
Proof. exact (or_elim (@lem3455228 _89520 _89534 t P x f x' h1) (fun h0 : term126 _89520 _89534 x' t P x f => @lem3455545 _89520 _89534 x' t P x f h0) (fun h0 : term142 _89520 _89534 P x f x' => @lem3455544 _89520 _89534 P x f x' h0)). Qed.
Lemma lem3455547 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term182 _89520 _89534 t P x f x') : (term182 _89520 _89534 t P x f x') = False.
Proof. exact (prop_ext (fun h2 : term182 _89520 _89534 t P x f x' => @lem3455546 _89520 _89534 t P x f x' h1) (fun h2 : False => @lem3455228 _89520 _89534 t P x f x' h1)). Qed.
Lemma lem3455548 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (x' : _89534) (h1 : term182 _89520 _89534 t P x f x') : False.
Proof. exact (EQ_MP (@lem3455547 _89520 _89534 t P x f x' h1) (@lem3455228 _89520 _89534 t P x f x' h1)). Qed.
Lemma lem3455549 {_89520 _89534 : Type'} (t : _89520 -> Prop) (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term185 _89520 _89534 t P x f) : False.
Proof. exact (ex_elim (@lem3455130 _89520 _89534 t P x f h1) (fun x' : _89534 => fun h0 : term184 _89520 _89534 t P x f x' => @lem3455548 _89520 _89534 t P x f x' h0)). Qed.
Lemma lem3455550 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term30 _89520 _89534 P x f) : False.
Proof. exact (ex_elim (@lem3455129 _89520 _89534 P x f h1) (fun t : _89520 -> Prop => fun h0 : term186 _89520 _89534 P x f t => @lem3455549 _89520 _89534 t P x f h0)). Qed.
Lemma lem3455551 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term30 _89520 _89534 P x f) : (term30 _89520 _89534 P x f) = False.
Proof. exact (prop_ext (fun h2 : term30 _89520 _89534 P x f => @lem3455550 _89520 _89534 P x f h1) (fun h2 : False => @lem3454628 _89520 _89534 P x f h1)). Qed.
Lemma lem3455552 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) (h1 : term30 _89520 _89534 P x f) : False.
Proof. exact (EQ_MP (@lem3455551 _89520 _89534 P x f h1) (@lem3454628 _89520 _89534 P x f h1)). Qed.
Lemma lem3455553 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : term29 _89520 _89534 P x f.
Proof. exact (fun h0 : term30 _89520 _89534 P x f => @lem3455552 _89520 _89534 P x f h0). Qed.
Lemma lem3455554 {_89520 _89534 : Type'} (P : _89534 -> Prop) (x : _89520) (f : type1470 _89520 _89534) : (term26 _89520 _89534 P f x) = (term19 _89520 _89534 P x f).
Proof. exact (EQ_MP (@lem3454627 _89520 _89534 P x f) (@lem3455553 _89520 _89534 P x f)). Qed.
Lemma lem3455559 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term1 _89520 _89534 P f.
Proof. exact (fun x : _89520 => @lem3455554 _89520 _89534 P x f). Qed.
Lemma lem3455564 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : term12 _89520 _89534 f.
Proof. exact (fun P : _89534 -> Prop => @lem3455559 _89520 _89534 P f). Qed.
Lemma lem3455569 {_89520 _89534 : Type'} : term16 _89520 _89534.
Proof. exact (fun f : type1470 _89520 _89534 => @lem3455564 _89520 _89534 f). Qed.
Lemma lem3455570 {_89520 _89534 : Type'} : term15 _89520 _89534.
Proof. exact (EQ_MP (@lem3454623 _89520 _89534) (@lem3455569 _89520 _89534)). Qed.
Lemma lem3455571 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : term239 _89520 _89534 f.
Proof. exact (@lem3455570 _89520 _89534 f). Qed.
Lemma lem3455572 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : (term239 _89520 _89534 f) = (term11 _89520 _89534 f).
Proof. exact (eq_refl (term239 _89520 _89534 f)). Qed.
Lemma lem3455573 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) : term11 _89520 _89534 f.
Proof. exact (EQ_MP (@lem3455572 _89520 _89534 f) (@lem3455571 _89520 _89534 f)). Qed.
Lemma lem3455574 {_89520 _89534 : Type'} (f : type1470 _89520 _89534) (P : _89534 -> Prop) : term240 _89520 _89534 f P.
Proof. exact (@lem3455573 _89520 _89534 f P). Qed.
Lemma lem3455575 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term240 _89520 _89534 f P) = (term2 _89520 _89534 P f).
Proof. exact (eq_refl (term240 _89520 _89534 f P)). Qed.
Lemma lem3455576 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term2 _89520 _89534 P f.
Proof. exact (EQ_MP (@lem3455575 _89520 _89534 P f) (@lem3455574 _89520 _89534 f P)). Qed.
Lemma lem3455578 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term2 _89520 _89534 P f.
Proof. exact (@lem3454395 _89520 _89534 P f (@lem3455576 _89520 _89534 P f)). Qed.
Lemma lem3455579 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term3 _89520 _89534 P f) : False.
Proof. exact (@lem3455578 _89520 _89534 P f (@lem3454379 _89520 _89534 P f h1)). Qed.
Lemma lem3455580 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term3 _89520 _89534 P f) : (term3 _89520 _89534 P f) = False.
Proof. exact (prop_ext (fun h2 : term3 _89520 _89534 P f => @lem3455579 _89520 _89534 P f h1) (fun h2 : False => @lem3454379 _89520 _89534 P f h1)). Qed.
Lemma lem3455581 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) (h1 : term3 _89520 _89534 P f) : False.
Proof. exact (EQ_MP (@lem3455580 _89520 _89534 P f h1) (@lem3454379 _89520 _89534 P f h1)). Qed.
Lemma lem3455582 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term2 _89520 _89534 P f.
Proof. exact (fun h0 : term3 _89520 _89534 P f => @lem3455581 _89520 _89534 P f h0). Qed.
Lemma lem3455583 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term1 _89520 _89534 P f.
Proof. exact (EQ_MP (@lem3454378 _89520 _89534 P f) (@lem3455582 _89520 _89534 P f)). Qed.
